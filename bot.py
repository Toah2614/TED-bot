#!/usr/bin/env python3
"""
Discord management bot for The Titan Elite Division Rocket League league.

Features
--------
* Team creation / deletion (auto-creates channels, roles and division categories)
* Roster management with single-team enforcement and automatic role sync
* Recruitment via DM offers / join requests with accept-decline buttons
* Non-playing staff management
* Free-agent / restricted-free-agent role automation
* Persistent JSON storage with atomic writes and off-loop file I/O

Setup
-----
Provide a Discord token via the ``DISCORD_TOKEN`` environment variable or a
local ``.env`` file containing ``DISCORD_TOKEN=...``. Requires the *Server
Members* privileged intent to be enabled in the Discord developer portal.
"""

from __future__ import annotations

import asyncio
import io
import json
import logging
import os
import re
import sys
import tempfile
import unicodedata
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urlsplit

import discord
from discord import app_commands, ui
from discord.ext import tasks

# --------------------------------------------------------------------------- #
# Configuration — every magic string the bot relies on lives here.
# --------------------------------------------------------------------------- #

DATA_FILE = Path(os.getenv("ECRL_DATA_FILE", "ecrl_data.json"))

# Roster-move log channels. Channels are matched by a *normalised* name — fancy
# fonts (𝑻𝒓𝒂𝒏𝒔𝒇𝒆𝒓𝒔), emoji and decorative brackets (『』) are all stripped
# before comparison — so the channels in the "Roster Moves" category are found
# no matter how they're styled. The value is the normalised token to match.
ROSTER_CHANNELS = {
    "transfers": "transfers",
    "signings": "newsignings",
    "history": "transferhistory",
    "released": "releasedplayers",
    "loans": "loandeals",
    "managerial": "managerialchanges",
    "promotion": "promotionrelegation",
    "window": "windowclosed",
}

FREE_AGENT_ROLE = "Free Agent"
RESTRICTED_FREE_AGENT_ROLE = "Restricted Free Agent"

ADMIN_ROLE_KEYWORDS = ("admin", "owner")

BOT_VERSION = "1.4.0 (2026-10-25)"

DEFAULT_DIVISIONS = ["SL3", "CL3", "PL3", "CH3", "TL2", "LL2", "SA2"]
DIVISIONS: list[str] = []
RANK_ORDER = [
    "Gold 3",
    "Platinum 1", "Platinum 2", "Platinum 3",
    "Diamond 1", "Diamond 2", "Diamond 3",
    "Champion 1", "Champion 2", "Champion 3",
    "Grand Champion 1", "Grand Champion 2", "Grand Champion 3",
    "Supersonic Legend 1900", "Supersonic Legend 2000+",
]
RANK_SHORTCUTS = {
    "G3": "Gold 3",
    "P1": "Platinum 1", "P2": "Platinum 2", "P3": "Platinum 3",
    "D1": "Diamond 1", "D2": "Diamond 2", "D3": "Diamond 3",
    "C1": "Champion 1", "C2": "Champion 2", "C3": "Champion 3",
    "GC1": "Grand Champion 1", "GC2": "Grand Champion 2", "GC3": "Grand Champion 3",
    "SSL": "Supersonic Legend 1900", "SSL1900": "Supersonic Legend 1900",
    "SSL2000": "Supersonic Legend 2000+", "SSL2000+": "Supersonic Legend 2000+",
}
STAFF_POSITIONS = [
    "Non-Playing Owner",
    "Non-Playing Manager",
    "Coach",
    "Assistant Coach",
    "Analyst",
]

REQUEST_TIMEOUT = 86_400  # seconds an accept/decline DM stays live (24h)

# A read-only channel created inside each division category ("EL Teams", …)
# that holds one auto-updating message listing every team's roster.
RECORDS_CHANNEL_SUFFIX = "rosters"  # each division gets a "(<division>) rosters" channel
FIXTURES_CHANNEL_SUFFIX = "fixtures"  # each division gets a "(<division>) fixtures" channel
RECORDS_INTERVAL_HOURS = 6
FREE_AGENT_INTERVAL_HOURS = 12  # default; overridable via /config free_agent_interval_hours

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(name)s: %(message)s",
)
log = logging.getLogger("ted")


def load_token() -> str:
    """Return the Discord token from the environment or a local ``.env`` file."""
    token = os.getenv("DISCORD_TOKEN")
    if not token and Path(".env").exists():
        for raw in Path(".env").read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            line = line.removeprefix("export ").strip()
            key, _, value = line.partition("=")
            if key.strip() == "DISCORD_TOKEN":
                token = value.strip().strip('"').strip("'")
                break
    if not token:
        log.error("No DISCORD_TOKEN found in the environment or a .env file.")
        sys.exit(1)
    return token


# --------------------------------------------------------------------------- #
# Persistence
# --------------------------------------------------------------------------- #

class DataStore:
    """JSON-backed storage with atomic, off-event-loop writes.

    The previous version blocked the event loop on every save and could corrupt
    the file if two writes overlapped. Writes now go to a temp file and are
    atomically renamed into place, serialised behind an ``asyncio.Lock``.
    """

    def __init__(self, path: Path) -> None:
        self.path = path
        self._lock = asyncio.Lock()
        self._needs_save = False
        self.data: dict[str, Any] = self._read()

    def _read(self) -> dict[str, Any]:
        data: dict[str, Any] = {}
        if self.path.exists():
            try:
                data = json.loads(self.path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, OSError) as exc:
                log.warning("Could not read %s (%s); starting empty.", self.path, exc)
        data.setdefault("teams", {})
        data.setdefault("players", {})
        data.setdefault("matches", {})
        data.setdefault("settings", {})
        s = data["settings"]
        legacy_l2_to_sl = False
        if "division_codes" not in s:
            self._needs_save = True
            legacy_leagues = s.setdefault("leagues", {})
            if not isinstance(legacy_leagues, dict):
                legacy_leagues = {}
                s["leagues"] = legacy_leagues
            active_legacy = [code for code in ("EL", "PL", "CS", "L1", "L2") if code in legacy_leagues]
            if "L2" in active_legacy and "SL" not in legacy_leagues:
                sl_config = legacy_leagues.pop("L2")
                if not isinstance(sl_config, dict):
                    sl_config = {}
                legacy_leagues["SL"] = sl_config
                active_legacy = ["SL"] + [code for code in active_legacy if code != "L2"]
                legacy_l2_to_sl = True
            s["division_codes"] = active_legacy or DEFAULT_DIVISIONS.copy()
            # Apply the league structure requested for this server to existing
            # installations the first time they load the new dynamic system.
            default_bands = {
                "SL": ("SSL+", ["Supersonic Legend 1900", "Supersonic Legend 2000+"]),
                "EL": ("GC2-3", ["Grand Champion 2", "Grand Champion 3"]),
                "PL": ("C3-GC1", ["Champion 3", "Grand Champion 1"]),
                "CS": ("C1-2", ["Champion 1", "Champion 2"]),
                "L1": ("D1-3", ["Diamond 1", "Diamond 2", "Diamond 3"]),
            }
            for code in s["division_codes"]:
                if code in default_bands:
                    band, ranks = default_bands[code]
                    league = legacy_leagues.setdefault(code, {})
                    if not isinstance(league, dict):
                        league = {}
                        legacy_leagues[code] = league
                    league.update({"rank_band": band, "ranks": ranks})
        s.setdefault("transfer_window_open", True)
        s.setdefault("rosters_locked", False)
        s.setdefault("league_name", "The Titan Elites Division")
        s.setdefault("records_channel", "ecrl-records")
        s.setdefault("audit_channel", "audit-log")
        s.setdefault("signing_approval_channel", "")  # blank = fall back to audit channel
        s.setdefault("points_win", 3)
        s.setdefault("points_loss", 0)
        s.setdefault("roster_max", 0)   # 0 = unlimited
        s.setdefault("roster_min", 0)   # informational/eligibility
        s.setdefault("current_season", 1)
        s.setdefault("match_counter", 0)
        s.setdefault("free_agent_channel", "free-agents")
        s.setdefault("free_agent_interval_hours", 12)
        s.setdefault("free_agent_ping", True)
        s.setdefault("free_agent_stagger_seconds", 20)
        s.setdefault("match_format", "BO5")
        # Interactive fixture workflow settings. Existing installations can use
        # these immediately; every field below is also migrated per-match.
        s.setdefault("match_channel_category_id", None)
        s.setdefault("match_archive_category_id", None)
        s.setdefault("fixture_channel_id", None)

        # League format. team_size = 2 makes this a 2v2 league (3 => 3v3, etc.).
        had_team_size = "team_size" in s
        s.setdefault("team_size", 2)
        if not had_team_size:
            # One-time upgrade for a pre-existing league: give it proper 2v2 roster
            # limits (a full 2-player lineup, up to 2 subs) if they were unbounded.
            if not s.get("roster_min"):
                s["roster_min"] = s["team_size"]
            if not s.get("roster_max"):
                s["roster_max"] = s["team_size"] * 2

        # Player cap: 5 per team. Applied once so it takes effect on the existing
        # league; the flag means a later /config roster_max change will stick.
        if not s.get("cap5_applied"):
            s["roster_max"] = 5
            s["cap5_applied"] = True

        # One-time rename to The Titan Elite Division (updates pre-existing data).
        if not s.get("renamed_ted"):
            s["league_name"] = "The Titan Elite Division"
            s["renamed_ted"] = True

        # One-time rebrand is scoped to The Titan Elites Division package.
        if not s.get("renamed_ecrl"):
            s["league_name"] = "The Titan Elites Division"
            s["renamed_ecrl"] = True

        # 2v2 format with a 5-player roster cap (one-time; later /config changes stick).
        if not s.get("format_2v2_applied"):
            s["team_size"] = 2
            s["roster_max"] = 5
            s["format_2v2_applied"] = True

        # Legacy data sometimes stored these as lists rather than id-keyed dicts.
        # Coerce so the rest of the code (and the migrations below) can rely on dicts.
        if isinstance(data.get("teams"), list):
            data["teams"] = {
                (t.get("name") or f"team{i}"): t
                for i, t in enumerate(data["teams"], 1) if isinstance(t, dict)
            }
        if isinstance(data.get("players"), list):
            data["players"] = {
                str(p.get("id") or f"p{i}"): p
                for i, p in enumerate(data["players"], 1) if isinstance(p, dict)
            }
        if isinstance(data.get("matches"), list):
            coerced: dict[str, Any] = {}
            for i, mm in enumerate(data["matches"], 1):
                if isinstance(mm, dict):
                    coerced[mm.get("id") or f"M{i}"] = mm
            data["matches"] = coerced
        if legacy_l2_to_sl:
            for team in data["teams"].values():
                if team.get("division") == "L2":
                    team["division"] = "SL"
            for match in data["matches"].values():
                if match.get("division") == "L2":
                    match["division"] = "SL"
            for player in data["players"].values():
                for key in ("last_division", "eligible_division"):
                    if player.get(key) == "L2":
                        player[key] = "SL"
            for section in ("records", "fixtures_msgs"):
                for per_guild in s.get(section, {}).values():
                    if "L2" in per_guild:
                        per_guild["SL"] = per_guild.pop("L2")
        # Keep the match counter ahead of any existing M-ids so new ids don't collide.
        max_n = 0
        for mid in data["matches"]:
            if isinstance(mid, str) and mid.startswith("M") and mid[1:].isdigit():
                max_n = max(max_n, int(mid[1:]))
        s["match_counter"] = max(s.get("match_counter", 0), max_n)

        # Migrate older records so missing fields never raise later.
        for team in data["teams"].values():
            team.setdefault("roster", [])
            team.setdefault("staff", {})
            team.setdefault("has_played_match", False)
            # Default the manager to "Playing" unless a team explicitly set it
            # to False before (e.g. via /set-playing). New and legacy teams
            # without this key will now show as Playing by default.
            team.setdefault("manager_playing", True)
        for player in data["players"].values():
            player.setdefault("goals", 0)
            player.setdefault("assists", 0)
            player.setdefault("mvps", 0)
            player.setdefault("appearances", 0)
            player.setdefault("clean_sheets", 0)
        for mid, match in data["matches"].items():
            match.setdefault("id", mid)
            match.setdefault("status", "scheduled")
            match.setdefault("team1", "?")
            match.setdefault("team2", "?")
            match.setdefault("score1", None)
            match.setdefault("score2", None)
            match.setdefault("division", None)
            match.setdefault("guild_id", None)
            match.setdefault("season", s.get("current_season", 1))
            match.setdefault("scheduled_for", None)
            match.setdefault("deadline", None)
            match.setdefault("matchweek", None)
            match.setdefault("reminded", False)
            match.setdefault("reminder_stages", [])
            match.setdefault("confirmations", [])
            match.setdefault("fixture_message_id", None)
            match.setdefault("fixture_channel_id", None)
            match.setdefault("match_channel_id", None)
            match.setdefault("player_stats_applied", False)
            match.setdefault("goals", {})
            match.setdefault("assists", {})
            match.setdefault("mvps", [])
            match.setdefault("clean_sheets", [])
        return data

    def _write(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", dir=self.path.parent or ".", delete=False
        ) as tmp:
            json.dump(self.data, tmp, indent=2, ensure_ascii=False)
            tmp_path = Path(tmp.name)
        tmp_path.replace(self.path)

    async def save(self) -> None:
        async with self._lock:
            await asyncio.to_thread(self._write)
            self._needs_save = False

    # -- convenience accessors ------------------------------------------------
    @property
    def teams(self) -> dict[str, Any]:
        return self.data["teams"]

    @property
    def players(self) -> dict[str, Any]:
        return self.data["players"]

    @property
    def window_open(self) -> bool:
        return self.data["settings"].get("transfer_window_open", True)

    @property
    def rosters_locked(self) -> bool:
        return self.data["settings"].get("rosters_locked", False)

    @property
    def settings(self) -> dict[str, Any]:
        return self.data["settings"]

    @property
    def matches(self) -> dict[str, Any]:
        return self.data["matches"]

    @property
    def season(self) -> int:
        return self.data["settings"].get("current_season", 1)

    def next_match_id(self) -> str:
        self.data["settings"]["match_counter"] = self.data["settings"].get("match_counter", 0) + 1
        return f"M{self.data['settings']['match_counter']}"

    def team(self, name: str) -> Optional[dict[str, Any]]:
        return self.teams.get(name)

    def team_names(self) -> list[str]:
        return sorted(self.teams)

    def find_member_team(self, member_id: int) -> Optional[str]:
        for name, team in self.teams.items():
            if member_id in team.get("roster", []):
                return name
        return None


# --------------------------------------------------------------------------- #
# Bot
# --------------------------------------------------------------------------- #

class TitanElitesBot(discord.Client):
    def __init__(self) -> None:
        # Only the intents we actually use. `members` is privileged and required
        # to fetch members and manage roles; message content is not needed for
        # slash commands.
        intents = discord.Intents.default()
        intents.members = True
        super().__init__(intents=intents)
        self.tree = app_commands.CommandTree(self)
        self.store = DataStore(DATA_FILE)

    async def setup_hook(self) -> None:
        if self.store._needs_save:
            await self.store.save()
        await self.tree.sync()
        log.info("Application commands synced.")
        if not update_division_records.is_running():
            update_division_records.start()
        if not match_reminder_loop.is_running():
            match_reminder_loop.start()
        # Persistent fixture controls are re-registered after every restart.
        for match_id, match in self.store.matches.items():
            if match.get("status") == "scheduled":
                self.add_view(FixtureConfirmationView(match_id))
        for user_id, pdata in self.store.players.items():
            message_id = pdata.get("verification_message_id")
            if pdata.get("verification_status") == "pending" and message_id:
                try:
                    self.add_view(
                        VerifyApprovalView(
                            int(user_id), pdata.get("rank"),
                            pdata.get("verification_league") or league_for_player(pdata),
                        ),
                        message_id=int(message_id),
                    )
                except (TypeError, ValueError):
                    log.warning("Could not restore verification controls for player %s.", user_id)
        self.add_view(LeagueDashboardView())
        if not free_agent_loop.is_running():
            # Drip one free-agent announcement using the saved administrator setting.
            interval_hours = max(1, int(self.store.settings.get(
                "free_agent_interval_hours", FREE_AGENT_INTERVAL_HOURS
            )))
            free_agent_loop.change_interval(hours=interval_hours)
            free_agent_loop.start()

    async def on_ready(self) -> None:
        name = self.store.settings.get("league_name", "The Titan Elite Division")
        log.info("%s bot online as %s (id=%s)", name, self.user, getattr(self.user, "id", "?"))
        for guild in self.guilds:
            # Remove any guild-scoped command copies so commands don't show twice
            # (global set is the single source of truth).
            try:
                if self.tree.get_commands(guild=guild):
                    self.tree.clear_commands(guild=guild)
                    await self.tree.sync(guild=guild)
            except discord.HTTPException:
                pass
            # Show the league name as the bot's nickname in each server.
            me = guild.me
            if me and me.nick != name[:32]:
                try:
                    await me.edit(nick=name[:32])
                except discord.HTTPException:
                    pass


bot = TitanElitesBot()
DIVISIONS[:] = [str(code).upper() for code in bot.store.settings.get("division_codes", DEFAULT_DIVISIONS)]


@bot.tree.error
async def on_app_command_error(
    interaction: discord.Interaction, error: app_commands.AppCommandError
) -> None:
    name = interaction.command.name if interaction.command else "unknown"
    log.exception("Error in /%s", name, exc_info=error)
    message = "⚠️ Something went wrong while running that command."
    try:
        if interaction.response.is_done():
            await interaction.followup.send(message, ephemeral=True)
        else:
            await interaction.response.send_message(message, ephemeral=True)
    except discord.HTTPException:
        pass


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def is_admin(interaction: discord.Interaction) -> bool:
    """Admin = guild administrator/manage-guild permission, or an admin/owner role.

    Uses interaction.permissions (sent by Discord in the payload) so it works even
    on a freshly added server where the member/role cache isn't populated yet."""
    # Permissions from the interaction payload — cache-independent, never crashes.
    perms = interaction.permissions
    if perms.administrator or perms.manage_guild:
        return True
    guild = interaction.guild
    if guild is not None and getattr(interaction.user, "id", None) == guild.owner_id:
        return True
    member = interaction.user
    if not isinstance(member, discord.Member):
        return False
    try:
        names = [r.name.lower() for r in member.roles if r is not None]
    except Exception:  # role cache incomplete on a brand-new guild
        return False
    return any(keyword in n for n in names for keyword in ADMIN_ROLE_KEYWORDS)


def can_review_verification(interaction: discord.Interaction) -> bool:
    """Allow server admins and the server's designated staff/reviewer roles."""
    if is_admin(interaction):
        return True
    member = interaction.user
    if not isinstance(member, discord.Member):
        return False
    reviewer_roles = {"staff", "head of staff", "league manager", "league director"}
    return any(_norm(role.name) in reviewer_roles for role in member.roles if role is not None)


async def get_or_create_role(guild: discord.Guild, name: str, **kwargs: Any) -> discord.Role:
    role = discord.utils.get(guild.roles, name=name)
    if role is None:
        role = await guild.create_role(name=name, **kwargs)
    return role


def find_free_agent_role(guild: discord.Guild, name: str) -> Optional[discord.Role]:
    return (discord.utils.get(guild.roles, name=name)
            or discord.utils.get(guild.roles, name=f"🔰 {name}"))


async def get_or_create_free_agent_role(
    guild: discord.Guild, name: str, **kwargs: Any
) -> discord.Role:
    role = find_free_agent_role(guild, name)
    if role is None:
        role = await guild.create_role(name=name, **kwargs)
    return role


async def get_or_create_category(guild: discord.Guild, name: str) -> discord.CategoryChannel:
    category = discord.utils.get(guild.categories, name=name)
    if category is None:
        category = await guild.create_category(name)
    return category


def _normalise_channel(name: str) -> str:
    """Strip fancy fonts, emoji and punctuation so channels match reliably."""
    return re.sub(r"[^a-z0-9]", "", unicodedata.normalize("NFKC", name).lower())


def find_log_channel(guild: discord.Guild, key: str) -> Optional[discord.TextChannel]:
    """Find a roster-move channel by its normalised name (see ROSTER_CHANNELS)."""
    target = ROSTER_CHANNELS.get(key)
    if not target:
        return None
    for channel in guild.text_channels:
        if _normalise_channel(channel.name) == target:
            return channel
    return None


async def log_move(
    guild: discord.Guild, keys: str | tuple[str, ...], message: str, *, color: Optional[discord.Color] = None
) -> None:
    """Post an embed to one or more roster-move channels (by ROSTER_CHANNELS key)."""
    if isinstance(keys, str):
        keys = (keys,)
    embed = discord.Embed(
        description=message,
        color=color or discord.Color.blue(),
        timestamp=datetime.now(timezone.utc),
    )
    for key in keys:
        channel = find_log_channel(guild, key)
        if channel is None:
            log.debug("Roster channel for %r not found in %s.", key, guild.name)
            continue
        try:
            await channel.send(embed=embed)
        except discord.HTTPException:
            log.warning("Failed to post to roster channel %r.", key)


def team_role_name(team_name: str, division: str) -> str:
    """Canonical team-role name, e.g. 'NOMAX Vortex (PD)'."""
    return f"{team_name} ({division})"


def resolve_team_role(member: discord.Member, team_name: str) -> Optional[discord.Role]:
    """Find a team's role by stored id first, falling back to its name."""
    team = bot.store.team(team_name) or {}
    role_id = team.get("role_id")
    if role_id:
        role = member.guild.get_role(role_id)
        if role:
            return role
    division = team.get("division")
    if division:
        role = discord.utils.get(member.guild.roles, name=team_role_name(team_name, division))
        if role:
            return role
    return discord.utils.get(member.guild.roles, name=team_name)


def guild_team_role(guild: discord.Guild, team_name: str) -> Optional[discord.Role]:
    """Resolve a team's role at the guild level (id first, then name variants)."""
    team = bot.store.team(team_name) or {}
    rid = team.get("role_id")
    if rid:
        role = guild.get_role(rid)
        if role:
            return role
    division = team.get("division")
    if division:
        role = discord.utils.get(guild.roles, name=team_role_name(team_name, division))
        if role:
            return role
    return discord.utils.get(guild.roles, name=team_name)


def team_mention(guild: discord.Guild, team_name: str) -> str:
    """A pingable role mention for the team, or its bold name if no role exists."""
    role = guild_team_role(guild, team_name)
    return role.mention if role else f"**{team_name}**"


async def add_team_role(member: discord.Member, team_name: str) -> None:
    role = resolve_team_role(member, team_name)
    if role:
        try:
            await member.add_roles(role, reason="Roster change")
        except discord.HTTPException:
            log.warning("Could not add role %s to %s.", team_name, member)


async def remove_team_role(member: discord.Member, team_name: str) -> None:
    role = resolve_team_role(member, team_name)
    if role and role in member.roles:
        try:
            await member.remove_roles(role, reason="Roster change")
        except discord.HTTPException:
            log.warning("Could not remove role %s from %s.", team_name, member)


async def assign_free_agent_role(member: discord.Member, team_name: str) -> str:
    """Give the appropriate free-agent role and strip the other one."""
    guild = member.guild
    team = bot.store.team(team_name) or {}
    has_played = team.get("has_played_match", False)

    # Remember the division they came from so free-agent posts can target the
    # right division's managers.
    division = team.get("division")
    if division:
        bot.store.players.setdefault(str(member.id), {})["last_division"] = division
        await bot.store.save()

    restricted = await get_or_create_free_agent_role(
        guild, RESTRICTED_FREE_AGENT_ROLE, color=discord.Color.orange()
    )
    free = await get_or_create_free_agent_role(guild, FREE_AGENT_ROLE, color=discord.Color.green())

    stale = [r for r in (restricted, free) if r in member.roles]
    if stale:
        await member.remove_roles(*stale, reason="Free-agent status update")

    target = restricted if has_played else free
    await member.add_roles(target, reason="Free-agent status update")
    return target.name


def manager_role_mentions(guild: discord.Guild, division: Optional[str]) -> str:
    """Mentions only the Team Manager role for one division."""
    wanted = []
    div_tokens = set(_norm(division).split()) if division else None
    for role in guild.roles:
        n = _norm(role.name)
        is_manager_role = "team manager" in n and "co manager" not in n
        if not is_manager_role:
            continue
        if div_tokens is None or div_tokens.intersection(n.split()):
            wanted.append(role.mention)
    return " ".join(wanted)


# --- Per-league integration config -------------------------------------------
# Tokens used to auto-detect this server's league channels/roles by name.
# ("acad" matches both "Academy" and the mis-spelled "Acadamy" role.)
LEAGUE_TOKENS = {code: code.lower() for code in DIVISIONS}


def _norm(text: str) -> str:
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9]+", " ", text.lower())).strip()


def is_tracker_profile_link(value: str) -> bool:
    """Accept a Rocket League Tracker Network profile URL, not a search page."""
    try:
        parts = urlsplit(value.strip())
    except ValueError:
        return False
    host = (parts.hostname or "").lower().rstrip(".")
    segments = [segment.lower() for segment in parts.path.split("/") if segment]
    if (parts.scheme.lower() != "https" or parts.username or parts.password or host not in {
            "rocketleague.tracker.network", "tracker.network"
    }):
        return False
    try:
        if parts.port is not None:
            return False
    except ValueError:
        return False
    try:
        profile_index = segments.index("profile")
        game_index = segments.index("rocket-league")
    except ValueError:
        return False
    return game_index < profile_index and profile_index + 2 < len(segments)


def tracker_profile_key(value: str) -> str:
    """Normalize a Tracker URL for duplicate-profile checks."""
    try:
        parts = urlsplit(value.strip())
    except ValueError:
        return value.strip().lower()
    return parts._replace(query="", fragment="").geturl().rstrip("/").lower()


def league_cfg(division: Optional[str]) -> dict:
    """Stored mapping for a league: rosters_channel, fa_channel, manager_role, co_manager_role (IDs)."""
    if not division:
        return {}
    return bot.store.settings.setdefault("leagues", {}).setdefault(division, {})


async def league_manager_role(guild: discord.Guild, division: str) -> discord.Role:
    """Use the mapped manager role, find a matching one, or create it once."""
    cfg = league_cfg(division)
    mapped = guild.get_role(cfg.get("manager_role")) if cfg.get("manager_role") else None
    if mapped:
        if not mapped.mentionable:
            try:
                await mapped.edit(mentionable=True, reason="Enable Team Manager free-agent pings")
            except discord.HTTPException:
                pass
        return mapped
    token = _norm(division).split()
    for role in guild.roles:
        name = _norm(role.name)
        if "team manager" in name and "co manager" not in name and any(t in name.split() for t in token):
            cfg["manager_role"] = role.id
            if not role.mentionable:
                try:
                    await role.edit(mentionable=True, reason="Enable Team Manager free-agent pings")
                except discord.HTTPException:
                    pass
            return role
    role = await get_or_create_role(
        guild, f"Team Manager {division}", color=discord.Color.gold(), mentionable=True
    )
    cfg["manager_role"] = role.id
    return role


async def league_co_manager_role(guild: discord.Guild, division: str) -> discord.Role:
    """Use or create the co-manager role for a league."""
    cfg = league_cfg(division)
    mapped = guild.get_role(cfg.get("co_manager_role")) if cfg.get("co_manager_role") else None
    if mapped:
        return mapped
    token = _norm(division).split()
    for role in guild.roles:
        name = _norm(role.name)
        if "co manager" in name and any(t in name.split() for t in token):
            cfg["co_manager_role"] = role.id
            return role
    role = await get_or_create_role(guild, f"Co Manager {division}", color=discord.Color.blue())
    cfg["co_manager_role"] = role.id
    return role


def configured_manager_mentions(guild: discord.Guild, division: Optional[str]) -> str:
    """Mention the configured Team Manager role for this league only."""
    cfg = league_cfg(division)
    mentions = []
    rid = cfg.get("manager_role")
    role = guild.get_role(rid) if rid else None
    if role:
        mentions.append(role.mention)
    return " ".join(mentions) if mentions else manager_role_mentions(guild, division)


def league_fa_channel(guild: discord.Guild, division: Optional[str]) -> Optional[discord.TextChannel]:
    """The configured free-agent channel for a league, else the global fallback channel."""
    cid = league_cfg(division).get("fa_channel")
    ch = guild.get_channel(cid) if cid else None
    if isinstance(ch, discord.TextChannel):
        return ch
    name = bot.store.settings.get("free_agent_channel") or "free-agents"
    target = _normalise_channel(name)
    return next((c for c in guild.text_channels if _normalise_channel(c.name) == target), None)


def find_team_category(guild: discord.Guild, division: Optional[str]) -> Optional[discord.CategoryChannel]:
    """The server's existing team-channel category for a league (e.g. 'A league Team
    channels', 'X league team chats'). Uses a configured override if set, else detects
    by name. Returns None if there isn't one."""
    cid = league_cfg(division).get("team_category")
    cat = guild.get_channel(cid) if cid else None
    if isinstance(cat, discord.CategoryChannel):
        return cat
    token = LEAGUE_TOKENS.get(division)
    if not token:
        return None
    for c in guild.categories:
        cn = _norm(c.name)
        if token in cn.split() and any(w in cn for w in ("team", "chat", "channel")):
            return c
    return None


def find_info_category(guild: discord.Guild, division: Optional[str]) -> Optional[discord.CategoryChannel]:
    """The league's main info category (e.g. 'A league') — not the team-channel one."""
    token = LEAGUE_TOKENS.get(division)
    if not token:
        return None
    for c in guild.categories:
        cn = _norm(c.name)
        if token in cn.split() and not any(w in cn for w in ("team", "chat", "channel", "free agent")):
            return c
    return None


def detect_fixtures_channel(guild: discord.Guild, division: Optional[str]) -> Optional[discord.TextChannel]:
    """Find the league's fixtures channel. Prefers a channel named with the league code
    (e.g. 'el-future-fixtures'); falls back to a fixtures channel in the info category.
    Prefers upcoming/future over full-season/rest and never a results channel."""
    token = LEAGUE_TOKENS.get(division)
    def pick(cands):
        return (next((c for c in cands if "future" in _norm(c.name) or "upcoming" in _norm(c.name)), None)
                or next((c for c in cands if not any(w in _norm(c.name) for w in ("full", "rest", "season"))), None)
                or (cands[0] if cands else None))
    if token:
        named = [c for c in guild.text_channels
                 if token in _norm(c.name).split()
                 and ("fixture" in _norm(c.name) or "future" in _norm(c.name))
                 and not any(w in _norm(c.name) for w in ("result", "live", "roster", "standing", "table"))]
        if named:
            return pick(named)
    cat = find_info_category(guild, division)
    if cat is None:
        return None
    return pick([c for c in cat.text_channels if "fixture" in _norm(c.name) and "result" not in _norm(c.name)])


def league_rosters_channel(guild: discord.Guild, division: Optional[str]) -> Optional[discord.TextChannel]:
    cid = league_cfg(division).get("rosters_channel")
    ch = guild.get_channel(cid) if cid else None
    return ch if isinstance(ch, discord.TextChannel) else None


def league_fixtures_channel(guild: discord.Guild, division: Optional[str]) -> Optional[discord.TextChannel]:
    cid = league_cfg(division).get("fixtures_channel")
    ch = guild.get_channel(cid) if cid else None
    return ch if isinstance(ch, discord.TextChannel) else None


_LEAGUE_SLUG = {code: code.lower() for code in DIVISIONS}


def refresh_division_state() -> None:
    """Reload the active league list and all name-matching tokens from settings."""
    global LEAGUE_TOKENS, _LEAGUE_SLUG
    configured = bot.store.settings.setdefault("division_codes", DEFAULT_DIVISIONS.copy())
    codes = list(dict.fromkeys(str(code).strip().upper() for code in configured if str(code).strip()))
    DIVISIONS[:] = codes[:25]
    LEAGUE_TOKENS = {code: code.lower() for code in DIVISIONS}
    _LEAGUE_SLUG = {code: code.lower() for code in DIVISIONS}


def expand_rank_band(value: str) -> list[str]:
    """Expand compact ranges such as C1-2, C3-GC1, and SSL+ into rank names."""
    raw = re.sub(r"\s+", "", value).upper()
    if raw in {"SSL+", "SSL", "SUPersonicLEGEND+".upper()}:
        return [rank for rank in RANK_ORDER if rank.startswith("Supersonic Legend")]

    def resolve(token: str, prefix: str = "") -> Optional[str]:
        token = token.upper()
        if token.isdigit() and prefix:
            token = prefix + token
        shortcut = RANK_SHORTCUTS.get(token)
        if shortcut:
            return shortcut
        normalized = re.sub(r"[^a-z0-9+]+", "", token.lower())
        return next((rank for rank in RANK_ORDER
                     if re.sub(r"[^a-z0-9+]+", "", rank.lower()) == normalized), None)

    parts = raw.split("-", 1)
    start = resolve(parts[0])
    if start is None:
        raise ValueError("Use a rank band such as `D1-3`, `C1-2`, `C3-GC1`, or `SSL+`.")
    if len(parts) == 1:
        return [start]
    match = re.match(r"([A-Z]+)\d+$", parts[0])
    prefix = match.group(1) if match else ""
    end = resolve(parts[1], prefix)
    if end is None:
        raise ValueError("The end of that rank band is not a supported Rocket League rank.")
    first, last = RANK_ORDER.index(start), RANK_ORDER.index(end)
    if first > last:
        raise ValueError("The rank band must go from the lower rank to the higher rank.")
    return RANK_ORDER[first:last + 1]


def league_for_rank(rank: Optional[str]) -> Optional[str]:
    """Return the configured league whose rank band contains this rank."""
    if not rank:
        return None
    for code in DIVISIONS:
        if rank in league_cfg(code).get("ranks", []):
            return code
    return None


def league_for_mmr(mmr: Optional[int], mode: Optional[str]) -> Optional[str]:
    """Return a configured MMR league for the selected playlist and rating."""
    if mmr is None or mode not in {"2v2", "3v3"}:
        return None
    try:
        rating = int(mmr)
    except (TypeError, ValueError):
        return None
    for code in DIVISIONS:
        cfg = league_cfg(code)
        if cfg.get("mode") != mode or cfg.get("min_mmr") is None:
            continue
        lower = int(cfg["min_mmr"])
        upper = cfg.get("max_mmr")
        if rating >= lower and (upper is None or rating <= int(upper)):
            return code
    return None


def league_for_player(pdata: dict[str, Any]) -> Optional[str]:
    """Resolve an MMR application first, falling back to the legacy rank field."""
    mode = pdata.get("playlist") or pdata.get("mode")
    mmr = pdata.get("mmr")
    if mode in {"2v2", "3v3"} and mmr is not None:
        return league_for_mmr(mmr, mode)
    return league_for_rank(pdata.get("rank"))


def league_display_name(code: Optional[str]) -> str:
    if not code:
        return "No active league"
    return str(league_cfg(code).get("display_name") or f"{code} League")


def mmr_band_label(cfg: dict[str, Any]) -> str:
    lower = cfg.get("min_mmr")
    upper = cfg.get("max_mmr")
    if lower is None:
        return str(cfg.get("rank_band") or "MMR range not set")
    return f"{lower}+ MMR" if upper is None else f"{lower}–{upper} MMR"


def league_autocomplete_choices() -> list[app_commands.Choice[str]]:
    choices = []
    for code in DIVISIONS[:25]:
        cfg = league_cfg(code)
        band = mmr_band_label(cfg) if cfg.get("min_mmr") is not None else cfg.get("rank_band")
        name = cfg.get("display_name") or code
        label = f"{name} ({code}) — {cfg.get('mode')} {band}" if cfg.get("mode") else f"{name} ({code}) — {band}" if band else name
        choices.append(app_commands.Choice(name=label[:100], value=code))
    return choices


async def division_autocomplete(
    interaction: discord.Interaction, current: str
) -> list[app_commands.Choice[str]]:
    needle = current.strip().lower()
    return [choice for choice in league_autocomplete_choices()
            if needle in choice.name.lower() or needle in choice.value.lower()][:25]


async def ensure_league_rosters_channel(guild: discord.Guild, division: Optional[str]) -> Optional[discord.TextChannel]:
    """Return this league's rosters channel — configured, or found by name, or newly
    created as '<league>-league-rosters' inside the league's info category."""
    ch = league_rosters_channel(guild, division)
    if ch:
        return ch
    token = LEAGUE_TOKENS.get(division)
    # find an existing rosters channel by name
    for c in guild.text_channels:
        n = _norm(c.name)
        if token and token in n.split() and "roster" in n:
            league_cfg(division)["rosters_channel"] = c.id
            return c
    info = find_info_category(guild, division)
    if info:
        for c in info.text_channels:
            if "roster" in _norm(c.name):
                league_cfg(division)["rosters_channel"] = c.id
                return c
        # create one in the league's info category
        slug = _LEAGUE_SLUG.get(division, str(division).lower())
        try:
            c = await guild.create_text_channel(f"{slug}-league-rosters", category=info, reason="Rosters channel")
        except discord.HTTPException:
            return None
        league_cfg(division)["rosters_channel"] = c.id
        await bot.store.save()
        return c
    return None


async def add_player_to_team(
    member: discord.Member, team_name: str, *, bypass_limits: bool = False,
    bypass_window: bool = False,
) -> tuple[bool, str]:
    """Add a member to a roster, enforcing single-team membership and syncing roles.

    Returns ``(success, human_readable_message)``. ``bypass_limits`` lets admin
    commands override the roster-size cap and roster lock.
    """
    team = bot.store.team(team_name)
    if team is None:
        return False, f"Team **{team_name}** no longer exists."
    eligibility_error = league_eligibility_error(member, team)
    if eligibility_error:
        return False, eligibility_error
    if member.id in team.get("roster", []):
        return False, f"{member.mention} is already on **{team_name}**."
    current = bot.store.find_member_team(member.id)
    if current and current != team_name:
        return False, f"{member.mention} is already on **{current}** and must `/leave` first."

    if not bypass_limits and not bypass_window and not bot.store.window_open:
        return False, "🔒 The transfer window is closed."
    if not bypass_limits:
        if bot.store.rosters_locked:
            return False, "🔒 Rosters are currently locked."
        roster_max = bot.store.settings.get("roster_max", 0)
        if roster_max and len(team.get("roster", [])) >= roster_max:
            return False, f"**{team_name}** is full (max {roster_max} players)."

    team.setdefault("roster", []).append(member.id)
    await bot.store.save()

    for role_name in (FREE_AGENT_ROLE, RESTRICTED_FREE_AGENT_ROLE):
        role = find_free_agent_role(member.guild, role_name)
        if role and role in member.roles:
            try:
                await member.remove_roles(role, reason="Signed to a team")
            except discord.HTTPException:
                pass
    await add_team_role(member, team_name)
    return True, f"{member.mention} joined **{team_name}**."


async def remove_player_from_team(member: discord.Member, team_name: str) -> bool:
    """Remove a member from a roster and strip the team role. Returns success."""
    team = bot.store.team(team_name)
    if not team or member.id not in team.get("roster", []):
        return False
    team["roster"].remove(member.id)
    await bot.store.save()
    await remove_team_role(member, team_name)
    return True


async def delete_team_resources(guild: discord.Guild, team_name: str) -> None:
    """Delete a team's channels, role and stored data."""
    team = bot.store.team(team_name)
    if not team:
        return
    for key, name_suffix in (("text_channel_id", "-talking"), ("voice_channel_id", "-vc")):
        channel = guild.get_channel(team.get(key)) if team.get(key) else None
        if channel is None:
            safe = team_name.lower().replace(" ", "-")
            channel = discord.utils.get(guild.channels, name=f"{safe}{name_suffix}")
        if channel:
            try:
                await channel.delete(reason=f"Team {team_name} deleted")
            except discord.HTTPException:
                log.warning("Could not delete channel for %s.", team_name)

    role = guild.get_role(team["role_id"]) if team.get("role_id") else discord.utils.get(
        guild.roles, name=team_name
    )
    if role:
        try:
            await role.delete(reason=f"Team {team_name} deleted")
        except discord.HTTPException:
            log.warning("Could not delete role for %s.", team_name)

    bot.store.teams.pop(team_name, None)
    await bot.store.save()


async def team_autocomplete(
    interaction: discord.Interaction, current: str
) -> list[app_commands.Choice[str]]:
    current = current.lower()
    return [
        app_commands.Choice(name=name, value=name)
        for name in bot.store.team_names()
        if current in name.lower()
    ][:25]


# --------------------------------------------------------------------------- #
# Division roster records (auto-updating channel per division)
# --------------------------------------------------------------------------- #

def format_label(division: Optional[str] = None) -> str:
    """Return a league's configured format, falling back to the server default."""
    cfg = league_cfg(division)
    n = cfg.get("team_size", bot.store.settings.get("team_size", 2))
    return f"{n}v{n}"


def _roster_field_value(team: dict[str, Any]) -> str:
    roster = team.get("roster", [])
    if not roster:
        return "*No players*"
    manager_id = team.get("manager")
    lines = [f"<@{uid}>" + (" 👑" if uid == manager_id else "") for uid in roster]
    text = "\n".join(lines)
    return text if len(text) <= 1024 else text[:1015].rsplit("\n", 1)[0] + "\n…"


def team_in_guild(guild: discord.Guild, name: str, team: dict[str, Any]) -> bool:
    """True if a team belongs to this server (its channels or role resolve here).

    Team data isn't stored per-guild, so this scopes each division board to the
    teams that actually live in the server being updated — no teams from other
    servers the bot happens to be in.
    """
    for key in ("text_channel_id", "voice_channel_id"):
        cid = team.get(key)
        if cid and guild.get_channel(cid):
            return True
    role_id = team.get("role_id")
    if role_id and guild.get_role(role_id):
        return True
    # Legacy teams created before IDs were stored: fall back to a role by name.
    division = team.get("division")
    if division and discord.utils.get(guild.roles, name=team_role_name(name, division)):
        return True
    return discord.utils.get(guild.roles, name=name) is not None


ROSTER_LEAGUES = {"A", "X"}   # only these leagues get auto-posted roster boards
RL_NAME_LEAGUES = {"X"}       # only these show Rocket League usernames on the roster


def _roster_line(uid: int, division: Optional[str]) -> str:
    """A roster entry: Discord mention, plus RL name for leagues that show it (X)."""
    base = f"<@{uid}>"
    if division in RL_NAME_LEAGUES:
        rl = bot.store.players.get(str(uid), {}).get("rl_name")
        if rl:
            return f"{base} — {rl}"
    return base


def build_team_card(guild: discord.Guild, name: str, team: dict[str, Any]) -> discord.Embed:
    """One roster card per team, styled like the league rosters channel:
    Manager (Playing/Not Playing), Co-Manager, Players, and a Members count."""
    manager_id = team.get("manager")
    division = team.get("division")
    playing = bool(team.get("manager_playing", True))
    staff = team.get("staff", {}) or {}

    co_ids: list[int] = []
    for position, ids in staff.items():
        if "co-manager" in position.lower() or "co manager" in position.lower():
            co_ids.extend(ids)

    roster = team.get("roster", [])
    exclude = set(co_ids) | ({manager_id} if manager_id else set())
    player_ids = [uid for uid in roster if uid not in exclude]

    e = discord.Embed(title=f"🔴 {name}", color=discord.Color.red())
    if team.get("logo"):
        e.set_thumbnail(url=team["logo"])
    tag = "Playing" if playing else "Not Playing"
    e.add_field(
        name=f"👑 Manager ({tag}) 👑",
        value=(_roster_line(manager_id, division) if manager_id else "*Vacant*"),
        inline=False,
    )
    if co_ids:
        e.add_field(name="🤝 Co-Manager 🤝",
                    value="\n".join(_roster_line(u, division) for u in co_ids), inline=False)
    e.add_field(
        name="🎮 Players 🎮",
        value="\n".join(_roster_line(u, division) for u in player_ids) if player_ids else "*None yet*",
        inline=False,
    )
    members = ({manager_id} if manager_id else set()) | set(co_ids) | set(player_ids)
    e.set_footer(text=f"👥 Members: {len(members)}")
    return e


def build_division_embeds(guild: discord.Guild, division: str) -> list[discord.Embed]:
    """A header embed plus one roster card per team in this division (image-1 style)."""
    teams = sorted(
        (n, t)
        for n, t in bot.store.teams.items()
        if t.get("division") == division and team_in_guild(guild, n, t)
    )
    now = datetime.now(timezone.utc)
    window = "🟢 Transfer window: OPEN" if bot.store.window_open else "🔴 Transfer window: CLOSED"
    header = discord.Embed(title=f"🏆 {league_display_name(division)} — Rosters",
                           description=window, color=discord.Color.blurple(), timestamp=now)
    header.set_footer(text=f"{format_label(division)} league · Auto-updates every {RECORDS_INTERVAL_HOURS} hours")
    if not teams:
        header.description = "No teams in this division yet."
        return [header]

    cards = [build_team_card(guild, n, t) for n, t in teams]
    # Discord allows max 10 embeds per message. Keep the header when there's room;
    # otherwise show as many team cards as fit.
    if len(cards) <= 9:
        return [header, *cards]
    return cards[:10]


async def ensure_records_channel(
    guild: discord.Guild, category: discord.CategoryChannel, division: str
) -> Optional[discord.TextChannel]:
    """Return (creating if needed) the read-only rosters channel for this division,
    pinned to the top of its category. Named like '(SL) rosters' and matched by
    normalised name, so an existing channel such as '(SL) Rosters' is reused."""
    channel_name = f"({division}) {RECORDS_CHANNEL_SUFFIX}"  # e.g. "(SL) rosters"
    target = _normalise_channel(channel_name)
    channel = None
    for existing in category.text_channels:
        if _normalise_channel(existing.name) == target:
            channel = existing
            break

    if channel is None:
        overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
            guild.me: discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_messages=True),
        }
        try:
            channel = await guild.create_text_channel(
                channel_name,
                category=category,
                overwrites=overwrites,
                topic=f"{division} division rosters — auto-updates every {RECORDS_INTERVAL_HOURS}h",
                reason="Division rosters channel",
            )
        except discord.HTTPException:
            log.warning("Could not create rosters channel in %s.", category.name)
            return None

    # Keep it at the top of the category (fixes channels created at the bottom).
    siblings = category.text_channels
    if siblings and siblings[0].id != channel.id:
        try:
            await channel.move(beginning=True, category=category)
        except discord.HTTPException:
            pass
    return channel


async def refresh_division_records(guild: discord.Guild) -> None:
    """Post or edit the roster message in each division's records channel."""
    settings = bot.store.data["settings"].setdefault("records", {})
    guild_records: dict[str, Any] = settings.setdefault(str(guild.id), {})
    changed = False

    for division in DIVISIONS:
        info = guild_records.get(division)
        # Post to the league's configured rosters channel; skip leagues that have none
        # (we never create roster channels — we only use existing ones).
        channel = league_rosters_channel(guild, division)
        if channel is None:
            continue

        embeds = build_division_embeds(guild, division)
        message = None
        if info and info.get("channel_id") == channel.id:
            try:
                message = await channel.fetch_message(info["message_id"])
            except (discord.NotFound, discord.HTTPException):
                message = None

        if message is not None:
            try:
                await message.edit(embeds=embeds)
            except discord.HTTPException:
                message = None

        if message is None:
            try:
                message = await channel.send(embeds=embeds)
            except discord.HTTPException:
                log.warning("Could not post records for %s.", division)
                continue
            guild_records[division] = {"channel_id": channel.id, "message_id": message.id}
            changed = True

    if changed:
        await bot.store.save()


def _fmt_date(iso: Optional[str]) -> str:
    """ISO datetime -> 'DD/MM/YYYY' (empty string if missing/bad)."""
    if not iso:
        return ""
    try:
        return datetime.fromisoformat(iso).strftime("%d/%m/%Y")
    except ValueError:
        return iso[:10]


def build_fixtures_content(guild: discord.Guild, division: str) -> str:
    """The auto-updating 'Future Games' board: every game week with team pings."""
    matches = [
        m for m in bot.store.matches.values()
        if m.get("guild_id") == guild.id
        and m.get("division") == division
        and m.get("season") == bot.store.season
    ]

    def _kick(m: dict[str, Any]) -> str:
        return m.get("scheduled_for") or ""

    upcoming = sorted(
        (m for m in matches if m.get("status") in ("scheduled", "reported", "disputed")),
        key=_kick,
    )
    done = sorted((m for m in matches if m.get("status") == "confirmed"), key=_kick)

    header = f"🏆 **{division} — Future Games**"
    if not matches:
        return f"{header}\n\nNo fixtures scheduled yet."

    by_week: dict[Any, list[dict[str, Any]]] = {}
    for m in upcoming:
        by_week.setdefault(m.get("matchweek"), []).append(m)

    parts = [header, ""]
    for week in sorted(by_week, key=lambda w: (w is None, w)):
        wk_matches = by_week[week]
        date = _fmt_date(wk_matches[0].get("scheduled_for"))
        label = f"GAME WEEK {week}" if week is not None else "UNSCHEDULED"
        parts.append(f"**{label}**" + (f"  📅 {date}" if date else ""))
        for m in wk_matches:
            tag = {"reported": " ⏳", "disputed": " ⚠️"}.get(m.get("status"), "")
            parts.append(
                f"{team_mention(guild, m.get('team1',''))} vs {team_mention(guild, m.get('team2',''))}{tag}"
            )
        parts.append("")

    if done:
        parts.append("━━━━━━━━━━━━━━━")
        parts.append("**Results**")
        for m in done[-8:]:
            ff = " 🏳️" if m.get("forfeit") else ""
            parts.append(
                f"{team_mention(guild, m.get('team1',''))} {m.get('score1')}–{m.get('score2')} "
                f"{team_mention(guild, m.get('team2',''))}{ff}"
            )

    content = "\n".join(parts).strip()
    if len(content) > 1990:
        content = content[:1980].rsplit("\n", 1)[0] + "\n…"
    return content


async def ensure_fixtures_channel(
    guild: discord.Guild, category: discord.CategoryChannel, division: str
) -> Optional[discord.TextChannel]:
    """Return (creating if needed) the read-only '(<division>) fixtures' channel."""
    channel_name = f"({division}) {FIXTURES_CHANNEL_SUFFIX}"
    target = _normalise_channel(channel_name)
    for existing in category.text_channels:
        if _normalise_channel(existing.name) == target:
            return existing
    overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
        guild.me: discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_messages=True),
    }
    try:
        return await guild.create_text_channel(
            channel_name,
            category=category,
            overwrites=overwrites,
            topic=f"{division} division fixtures & results — auto-updated",
            reason="Division fixtures channel",
        )
    except discord.HTTPException:
        log.warning("Could not create fixtures channel in %s.", category.name)
        return None


async def refresh_division_fixtures(guild: discord.Guild) -> None:
    """Post or edit the fixtures message in each division's fixtures channel."""
    settings = bot.store.data["settings"].setdefault("fixtures_msgs", {})
    guild_fx: dict[str, Any] = settings.setdefault(str(guild.id), {})
    changed = False

    for division in DIVISIONS:
        # Post to the league's configured fixtures channel; skip leagues without one.
        channel = league_fixtures_channel(guild, division)
        if channel is None:
            continue
        info = guild_fx.get(division)

        content = build_fixtures_content(guild, division)
        silent = discord.AllowedMentions.none()  # pills show, but edits never ping
        message = None
        if info and info.get("channel_id") == channel.id:
            try:
                message = await channel.fetch_message(info["message_id"])
            except (discord.NotFound, discord.HTTPException):
                message = None
        if message is not None:
            try:
                await message.edit(content=content, allowed_mentions=silent)
            except discord.HTTPException:
                message = None
        if message is None:
            try:
                message = await channel.send(content=content, allowed_mentions=silent)
            except discord.HTTPException:
                log.warning("Could not post fixtures for %s.", division)
                continue
            guild_fx[division] = {"channel_id": channel.id, "message_id": message.id}
            changed = True

    if changed:
        await bot.store.save()


@tasks.loop(hours=RECORDS_INTERVAL_HOURS)
async def update_division_records() -> None:
    for guild in bot.guilds:
        try:
            await refresh_division_records(guild)
            await refresh_division_fixtures(guild)
        except Exception:  # noqa: BLE001 — keep the loop alive across guilds
            log.exception("Failed to refresh boards for guild %s.", guild.id)


@update_division_records.before_loop
async def _before_records_loop() -> None:
    await bot.wait_until_ready()


# --------------------------------------------------------------------------- #
# Audit log
# --------------------------------------------------------------------------- #

# Commands whose use is recorded to the audit-log channel.
AUDITED_COMMANDS = {
    "create-team", "delete-team", "rename-team", "set-manager", "transfer",
    "promote", "relegate", "team_add_player", "team_kick_player", "release_player",
    "add_staff", "remove_staff", "set-team-played", "loan",
    "close-transfer-window", "open-transfer-window", "schedule", "report-result",
    "confirm-result", "dispute-result", "forfeit", "cancel-match",
    "season-start", "config", "sync",
    "reschedule", "edit-result", "clear-fixtures", "generate-fixtures", "announce", "post-fixtures",
}


async def write_audit(guild: discord.Guild, message: str) -> None:
    name = bot.store.settings.get("audit_channel") or ""
    if not name:
        return
    target = _normalise_channel(name)
    channel = next((c for c in guild.text_channels if _normalise_channel(c.name) == target), None)
    if channel is None:
        return
    embed = discord.Embed(description=message, color=discord.Color.dark_grey(), timestamp=datetime.now(timezone.utc))
    try:
        await channel.send(embed=embed)
    except discord.HTTPException:
        pass


@bot.event
async def on_app_command_completion(
    interaction: discord.Interaction, command: app_commands.Command
) -> None:
    if interaction.guild is None or command.name not in AUDITED_COMMANDS:
        return
    params = interaction.namespace.__dict__
    arg_bits = []
    for key, value in params.items():
        if isinstance(value, (discord.Member, discord.User)):
            value = value.mention
        elif isinstance(value, app_commands.Choice):
            value = value.value
        arg_bits.append(f"{key}={value}")
    args = " ".join(arg_bits)
    await write_audit(
        interaction.guild,
        f"🛠️ {interaction.user.mention} used `/{command.name}`" + (f" — {args}" if args else ""),
    )


@bot.event
async def on_member_remove(member: discord.Member) -> None:
    """When someone leaves the server, remove them from any team (roster, staff,
    and the manager slot), refresh the division roster boards, and log it."""
    guild = member.guild
    affected: set[str] = set()
    for name, team in bot.store.teams.items():
        if (member.id in team.get("roster", [])
                or team.get("manager") == member.id
                or any(member.id in ids for ids in team.get("staff", {}).values())):
            affected.add(name)
    if not affected:
        return

    vacated_manager: list[str] = []
    for name in affected:
        team = bot.store.team(name)
        if not team:
            continue
        if member.id in team.get("roster", []):
            team["roster"].remove(member.id)
        for position, ids in list(team.get("staff", {}).items()):
            if member.id in ids:
                ids.remove(member.id)
                if not ids:
                    team["staff"].pop(position, None)
        if team.get("manager") == member.id:
            team["manager"] = None
            vacated_manager.append(name)
    await bot.store.save()

    try:
        await refresh_division_records(guild)
    except Exception:  # never let a display error swallow the cleanup
        log.exception("Failed to refresh roster boards after %s left.", member)

    for name in sorted(affected):
        await log_move(
            guild, "transfers",
            f"📤 {member.mention} left the server and was removed from **{name}**.",
        )
    for name in sorted(vacated_manager):
        await log_move(
            guild, "managerial",
            f"⚠️ **{name}** has no manager — its manager left the server. Assign a new one with `/set-manager`.",
            color=discord.Color.orange(),
        )


# --------------------------------------------------------------------------- #
# Standings (computed from confirmed matches)
# --------------------------------------------------------------------------- #

def compute_standings(guild: discord.Guild, division: str) -> list[dict[str, Any]]:
    """Return a sorted standings table for a division's current-season matches."""
    settings = bot.store.settings
    pts_win = settings.get("points_win", 3)
    pts_loss = settings.get("points_loss", 0)
    season = bot.store.season

    # Seed every team in the division that belongs to this guild.
    table: dict[str, dict[str, Any]] = {}
    for name, team in bot.store.teams.items():
        if team.get("division") == division and team_in_guild(guild, name, team):
            table[name] = {"team": name, "P": 0, "W": 0, "L": 0, "GF": 0, "GA": 0, "Pts": 0}

    for match in bot.store.matches.values():
        if (
            match.get("status") != "confirmed"
            or match.get("division") != division
            or match.get("season") != season
            or match.get("guild_id") != guild.id
        ):
            continue
        t1, t2 = match["team1"], match["team2"]
        s1, s2 = match.get("score1", 0), match.get("score2", 0)
        for tname in (t1, t2):
            table.setdefault(tname, {"team": tname, "P": 0, "W": 0, "L": 0, "GF": 0, "GA": 0, "Pts": 0})
        table[t1]["P"] += 1
        table[t2]["P"] += 1
        table[t1]["GF"] += s1; table[t1]["GA"] += s2
        table[t2]["GF"] += s2; table[t2]["GA"] += s1
        if s1 > s2:
            table[t1]["W"] += 1; table[t1]["Pts"] += pts_win
            table[t2]["L"] += 1; table[t2]["Pts"] += pts_loss
        elif s2 > s1:
            table[t2]["W"] += 1; table[t2]["Pts"] += pts_win
            table[t1]["L"] += 1; table[t1]["Pts"] += pts_loss

    rows = list(table.values())
    rows.sort(key=lambda r: (r["Pts"], r["GF"] - r["GA"], r["GF"], r["W"]), reverse=True)
    return rows


def format_standings_table(rows: list[dict[str, Any]]) -> str:
    """Monospace standings table."""
    header = f"{'#':<3}{'Team':<18}{'P':>3}{'W':>3}{'L':>3}{'GD':>5}{'Pts':>5}"
    lines = [header, "─" * len(header)]
    for i, r in enumerate(rows, 1):
        gd = r["GF"] - r["GA"]
        name = (r["team"][:17]) if len(r["team"]) > 17 else r["team"]
        lines.append(f"{i:<3}{name:<18}{r['P']:>3}{r['W']:>3}{r['L']:>3}{gd:>+5}{r['Pts']:>5}")
    return "```\n" + "\n".join(lines) + "\n```"


# --------------------------------------------------------------------------- #
# Matches
# --------------------------------------------------------------------------- #

def match_label(match: dict[str, Any]) -> str:
    when = match.get("scheduled_for", "")
    when = f" · {when[:16].replace('T', ' ')}" if when else ""
    return f"{match['id']}: {match['team1']} vs {match['team2']} [{match['status']}]{when}"


async def match_autocomplete(
    interaction: discord.Interaction, current: str
) -> list[app_commands.Choice[str]]:
    current = current.lower()
    out = []
    for m in sorted(bot.store.matches.values(), key=lambda x: x["id"], reverse=True):
        if interaction.guild and m.get("guild_id") != interaction.guild.id:
            continue
        label = match_label(m)
        if current in label.lower():
            out.append(app_commands.Choice(name=label[:100], value=m["id"]))
        if len(out) >= 25:
            break
    return out


async def apply_match_result(guild: discord.Guild, match: dict[str, Any]) -> None:
    """Mark both teams as having played and refresh standings records."""
    for tname in (match["team1"], match["team2"]):
        team = bot.store.team(tname)
        if team:
            team["has_played_match"] = True
    await bot.store.save()


@tasks.loop(minutes=10)
async def match_reminder_loop() -> None:
    now = datetime.now(timezone.utc)
    changed = False
    for match in bot.store.matches.values():
        if match.get("status") != "scheduled":
            continue
        when = match.get("scheduled_for")
        if not when:
            continue
        try:
            kickoff = datetime.fromisoformat(when)
        except ValueError:
            continue
        if kickoff.tzinfo is None:
            kickoff = kickoff.replace(tzinfo=timezone.utc)
        delta = (kickoff - now).total_seconds()
        stages = [(86400, "📅 Match Tomorrow! Please confirm your lineup."), (3600, "⏰ Match starts in ONE HOUR."), (1800, "⏰ Match starts in 30 minutes."), (600, "🚨 Match begins in 10 minutes.")]
        sent = set(match.get("reminder_stages", []))
        for seconds, text in stages:
            if seconds in sent or not (0 <= delta <= seconds):
                continue
            guild = bot.get_guild(match.get("guild_id"))
            if guild is None:
                break
            for tname in (match["team1"], match["team2"]):
                team = bot.store.team(tname)
                role = guild.get_role(team.get("role_id")) if team and team.get("role_id") else None
                ch = guild.get_channel(team.get("text_channel_id")) if team and team.get("text_channel_id") else None
                if ch:
                    mention = role.mention if role else ""
                    try:
                        await ch.send(
                            f"{mention} {text}\n{team_mention(guild, match['team1'])} vs "
                            f"{team_mention(guild, match['team2'])} — **{when[:16].replace('T', ' ')} UTC**.",
                            allowed_mentions=discord.AllowedMentions(roles=True, users=False, everyone=False),
                        )
                    except discord.HTTPException:
                        pass
            match.setdefault("reminder_stages", []).append(seconds)
            changed = True
    if changed:
        await bot.store.save()


@match_reminder_loop.before_loop
async def _before_reminder_loop() -> None:
    await bot.wait_until_ready()


# --------------------------------------------------------------------------- #
# Free-agent announcements
# --------------------------------------------------------------------------- #

def collect_free_agents(guild: discord.Guild) -> list[tuple[discord.Member, bool]]:
    """Return (member, is_restricted) for everyone holding a free-agent role
    who isn't currently on a team."""
    free_role = find_free_agent_role(guild, FREE_AGENT_ROLE)
    restricted_role = find_free_agent_role(guild, RESTRICTED_FREE_AGENT_ROLE)
    out: list[tuple[discord.Member, bool]] = []
    seen: set[int] = set()
    for role, restricted in ((restricted_role, True), (free_role, False)):
        if not role:
            continue
        for member in role.members:
            active_team = any(
                member.id in team.get("roster", []) and team_in_guild(guild, name, team)
                for name, team in bot.store.teams.items()
            )
            pdata = bot.store.players.get(str(member.id), {})
            division = free_agent_division(member, pdata)
            eligible = bool(division and not league_eligibility_error(member, {"division": division}))
            if member.id in seen or active_team or not eligible:
                continue
            seen.add(member.id)
            out.append((member, restricted))
    return out


async def post_free_agents(guild: discord.Guild) -> int:
    """Post one 'Free Agent Available' announcement per free agent into that
    player's league free-agent channel, pinging that league's manager roles."""
    settings = bot.store.settings

    def _is_old(msg: discord.Message) -> bool:
        return (
            msg.author == guild.me
            and bool(msg.embeds)
            and "Free Agent Available" in (msg.embeds[0].title or "")
        )

    agents = collect_free_agents(guild)
    if not agents:
        return 0

    ping = settings.get("free_agent_ping", True)
    stagger = max(0, int(settings.get("free_agent_stagger_seconds", 20)))

    # Resolve each agent's league channel once, then clear the previous batch
    # in each channel that will be used (needs Manage Messages).
    resolved = []
    channels_used = set()
    for member, restricted in agents[:25]:
        pdata = bot.store.players.get(str(member.id), {})
        division = free_agent_division(member, pdata)
        channel = league_fa_channel(guild, division)
        resolved.append((member, restricted, division, channel, pdata.get("rank")))
        if channel:
            channels_used.add(channel)
    for ch in channels_used:
        try:
            await ch.purge(limit=100, check=_is_old)
        except (discord.Forbidden, discord.HTTPException):
            pass

    posted = 0
    for i, (member, restricted, division, channel, rank) in enumerate(resolved):
        if channel is None:
            continue
        mentions = configured_manager_mentions(guild, division) if (ping and division) else ""
        status = "**Restricted Free Agent**" if restricted else "**Free Agent**"
        intro = (
            f"{member.mention} is **{rank}** and is currently a {status}."
            if rank else f"{member.mention} is currently a {status}."
        )
        if division:
            intro += f"\nLeague: **{league_display_name(division)}** · {format_label(division)}"
        embed = discord.Embed(
            title="📣 Free Agent Available",
            description=f"{intro}\n\nWould anyone like to sign them for their team?",
            color=discord.Color.purple(),
        )
        content = " ".join(x for x in (member.mention, mentions) if x)
        allowed = discord.AllowedMentions(roles=bool(mentions), users=True, everyone=False)
        try:
            await channel.send(content=content or None, embed=embed, allowed_mentions=allowed)
            posted += 1
        except discord.HTTPException:
            log.warning("Could not post free-agent announcement in %s.", guild.name)
        if stagger and i < len(resolved) - 1:
            await asyncio.sleep(stagger)
    return posted


def free_agent_division(member: discord.Member, pdata: dict[str, Any]) -> Optional[str]:
    """Prefer the member's MMR/rank league when its eligibility role is held."""
    held_roles = set(getattr(member, "roles", []))
    rank_division = league_for_player(pdata)
    if rank_division:
        return rank_division
    for division in DIVISIONS:
        role = _find_eligible_role(member.guild, division)
        if role and role in held_roles:
            return division
    if rank_division:
        return rank_division
    division = pdata.get("last_division")
    if division in DIVISIONS:
        return division
    return None


async def post_next_free_agent(guild: discord.Guild) -> bool:
    """Post ONE free-agent announcement per call (a slow drip), pinging that
    player's division Team Manager. Rotates through the pool over successive calls."""
    settings = bot.store.settings
    agents = collect_free_agents(guild)
    if not agents:
        return False

    rotation = settings.setdefault("fa_rotation", {})
    idx = int(rotation.get(str(guild.id), 0)) % len(agents)
    member, restricted = agents[idx]
    rotation[str(guild.id)] = (idx + 1) % len(agents)  # advance for next call

    pdata = bot.store.players.get(str(member.id), {})
    rank = pdata.get("rank")
    division = free_agent_division(member, pdata)

    channel = league_fa_channel(guild, division)  # per-league channel, else global fallback
    if channel is None:
        return False
    ping = settings.get("free_agent_ping", True)
    mentions = configured_manager_mentions(guild, division) if (ping and division) else ""

    status = "**Restricted Free Agent**" if restricted else "**Free Agent**"
    intro = (
        f"{member.mention} is **{rank}** and is currently a {status}."
        if rank else f"{member.mention} is currently a {status}."
    )
    if division:
        intro += f"\nLeague: **{league_display_name(division)}** · {format_label(division)}"
    embed = discord.Embed(
        title="📣 Free Agent Available",
        description=f"{intro}\n\nWould anyone like to sign them for their team?",
        color=discord.Color.purple(),
    )
    content = " ".join(x for x in (member.mention, mentions) if x)
    allowed = discord.AllowedMentions(roles=bool(mentions), users=True, everyone=False)
    try:
        await channel.send(content=content or None, embed=embed, allowed_mentions=allowed)
    except discord.HTTPException:
        log.warning("Could not post free-agent announcement in %s.", guild.name)
        return False
    await bot.store.save()  # persist the rotation pointer
    return True


@tasks.loop(hours=FREE_AGENT_INTERVAL_HOURS)
async def free_agent_loop() -> None:
    for guild in bot.guilds:
        try:
            await post_next_free_agent(guild)
        except Exception:  # noqa: BLE001 — keep the loop alive across guilds
            log.exception("Free-agent broadcast failed for guild %s.", guild.id)


@free_agent_loop.before_loop
async def _before_fa_loop() -> None:
    await bot.wait_until_ready()


# --------------------------------------------------------------------------- #
# Interactive views
# --------------------------------------------------------------------------- #

class JoinRequestView(ui.View):
    """Sent to a manager's DMs when a player requests to join their team."""

    def __init__(self, player: discord.Member, team: str) -> None:
        super().__init__(timeout=REQUEST_TIMEOUT)
        self.player = player
        self.team = team

    @ui.button(label="Accept", emoji="✅", style=discord.ButtonStyle.success)
    async def accept(self, interaction: discord.Interaction, button: ui.Button) -> None:
        success, message = await add_player_to_team(self.player, self.team)
        if success:
            await log_move(
                self.player.guild,
                ("transfers", "signings"),
                f"📥 {message} (accepted by {interaction.user.mention})",
                color=discord.Color.green(),
            )
        prefix = "✅ " if success else "⚠️ "
        await interaction.response.edit_message(content=prefix + message, view=None)
        self.stop()

    @ui.button(label="Decline", emoji="❌", style=discord.ButtonStyle.danger)
    async def decline(self, interaction: discord.Interaction, button: ui.Button) -> None:
        await interaction.response.edit_message(content="❌ Request declined.", view=None)
        self.stop()


class SignApprovalView(ui.View):
    """Posted to staff after a player accepts; a staff/admin confirms the signing."""

    def __init__(self, player: discord.Member, team: str, manager: discord.Member,
                 bypass_window: bool = False) -> None:
        super().__init__(timeout=None)
        self.player = player
        self.team = team
        self.manager = manager
        self.bypass_window = bypass_window

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if not is_admin(interaction):
            await interaction.response.send_message("❌ Only staff/admins can confirm signings.", ephemeral=True)
            return False
        return True

    @ui.button(label="Confirm Signing", emoji="✅", style=discord.ButtonStyle.success)
    async def confirm(self, interaction: discord.Interaction, button: ui.Button) -> None:
        current = bot.store.find_member_team(self.player.id)
        if current:
            return await interaction.response.edit_message(
                content=f"⚠️ {self.player.mention} is already on **{current}**.", view=None)
        eligibility_error = league_eligibility_error(self.player, bot.store.team(self.team) or {})
        if eligibility_error:
            return await interaction.response.edit_message(content=f"❌ {eligibility_error}", view=None)
        if not bot.store.window_open and not self.bypass_window:
            return await interaction.response.edit_message(content="🔒 The transfer window is closed.", view=None)
        success, message = await add_player_to_team(
            self.player, self.team, bypass_window=self.bypass_window
        )
        if success:
            await log_move(
                interaction.guild, ("transfers", "signings"),
                f"📥 {self.player.mention} signed for **{self.team}** "
                f"(offer by {self.manager.mention}, confirmed by {interaction.user.mention})",
                color=discord.Color.green())
            try:
                await self.player.send(f"✅ Your signing to **{self.team}** was confirmed by staff. Welcome!")
            except discord.HTTPException:
                pass
        await interaction.response.edit_message(
            content=(f"✅ Confirmed: {self.player.mention} → **{self.team}**." if success else f"⚠️ {message}"),
            view=None)
        self.stop()

    @ui.button(label="Reject", emoji="❌", style=discord.ButtonStyle.danger)
    async def reject(self, interaction: discord.Interaction, button: ui.Button) -> None:
        await interaction.response.edit_message(
            content=f"🚫 Signing of {self.player.mention} to **{self.team}** rejected by {interaction.user.mention}.",
            view=None)
        try:
            await self.player.send(f"🚫 Your signing to **{self.team}** wasn't approved by staff.")
        except discord.HTTPException:
            pass
        self.stop()


def resolve_staff_channel(guild: discord.Guild) -> Optional[discord.TextChannel]:
    """Where signing-approval requests are posted: the configured admin/audit channel."""
    for key in ("signing_approval_channel", "audit_channel"):
        name = bot.store.settings.get(key)
        if not name:
            continue
        target = _normalise_channel(name)
        ch = next((c for c in guild.text_channels if _normalise_channel(c.name) == target), None)
        if ch:
            return ch
    return None


class SignOfferView(ui.View):
    """Sent to a player's DMs when a manager offers them a roster spot."""

    def __init__(self, player: discord.Member, team: str, manager: discord.Member,
                 origin_channel_id: Optional[int] = None, *, bypass_window: bool = False) -> None:
        super().__init__(timeout=REQUEST_TIMEOUT)
        self.player = player
        self.team = team
        self.manager = manager
        self.origin_channel_id = origin_channel_id
        self.bypass_window = bypass_window

    @ui.button(label="Accept Offer", emoji="✅", style=discord.ButtonStyle.success)
    async def accept(self, interaction: discord.Interaction, button: ui.Button) -> None:
        guild = self.player.guild
        if interaction.user.id != self.player.id:
            return await interaction.response.send_message("❌ This offer is only for the player it was sent to.", ephemeral=True)
        if bot.store.find_member_team(self.player.id):
            return await interaction.response.edit_message(content="❌ You're already on a team.", view=None)
        eligibility_error = league_eligibility_error(self.player, bot.store.team(self.team) or {})
        if eligibility_error:
            return await interaction.response.edit_message(content=f"❌ {eligibility_error}", view=None)
        if not bot.store.window_open and not self.bypass_window:
            return await interaction.response.edit_message(content="🔒 The transfer window is closed.", view=None)
        # Player accepting sends the signing to staff for final confirmation.
        staff_channel = resolve_staff_channel(guild)
        if staff_channel is None and self.origin_channel_id:
            ch = guild.get_channel(self.origin_channel_id)
            if isinstance(ch, discord.TextChannel):
                staff_channel = ch
        if staff_channel is None:
            return await interaction.response.edit_message(
                content="✅ You accepted — but no staff channel is set for confirmations. "
                        "Ask an admin to set one with `/config signing_approval_channel <name>`.",
                view=None)
        embed = discord.Embed(
            title="📝 Signing Pending Approval",
            description=f"{self.player.mention} accepted an offer from {self.manager.mention} "
                        f"to join **{self.team}**.\nA staff member must confirm this signing.",
            color=discord.Color.orange(),
        )
        try:
            await staff_channel.send(
                embed=embed,
                view=SignApprovalView(self.player, self.team, self.manager, self.bypass_window),
            )
        except discord.HTTPException:
            return await interaction.response.edit_message(
                content="✅ You accepted, but I couldn't reach the staff channel. Ask an admin to check my permissions.",
                view=None)
        await interaction.response.edit_message(
            content=f"✅ You accepted the offer from **{self.team}**! It's now pending staff confirmation.",
            view=None)
        self.stop()

    @ui.button(label="Decline", emoji="❌", style=discord.ButtonStyle.danger)
    async def decline(self, interaction: discord.Interaction, button: ui.Button) -> None:
        await interaction.response.edit_message(content="❌ Offer declined.", view=None)
        self.stop()


class ConfirmDeleteView(ui.View):
    def __init__(self, team_name: str) -> None:
        super().__init__(timeout=60)
        self.team_name = team_name

    @ui.button(label="Confirm Delete", style=discord.ButtonStyle.danger)
    async def confirm(self, interaction: discord.Interaction, button: ui.Button) -> None:
        await interaction.response.defer(ephemeral=True)
        await delete_team_resources(interaction.guild, self.team_name)
        await interaction.followup.send(f"🗑️ **{self.team_name}** deleted.", ephemeral=True)
        self.stop()

    @ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, button: ui.Button) -> None:
        await interaction.response.edit_message(content="Cancelled.", view=None)
        self.stop()

    async def on_error(
        self, interaction: discord.Interaction, error: Exception, item: ui.Item
    ) -> None:
        log.exception("Delete confirmation failed for %s.", self.team_name)
        msg = (
            f"⚠️ Couldn't fully delete **{self.team_name}** — I may lack **Manage Channels**/"
            "**Manage Roles**, or my role sits below the team role. Fix that and try again."
        )
        try:
            if interaction.response.is_done():
                await interaction.followup.send(msg, ephemeral=True)
            else:
                await interaction.response.send_message(msg, ephemeral=True)
        except discord.HTTPException:
            pass


# --------------------------------------------------------------------------- #
# Team administration commands
# --------------------------------------------------------------------------- #

@bot.tree.command(name="create-team", description="Create a new team with its role & channels (Admin only)")
@app_commands.guild_only()
@app_commands.describe(
    team_name="Unique team name", manager="Team manager", division="League"
)
@app_commands.autocomplete(division=division_autocomplete)
async def create_team(
    interaction: discord.Interaction,
    team_name: str,
    manager: discord.Member,
    division: str,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)

    team_name = team_name.strip()
    if not team_name:
        return await interaction.response.send_message(
            "❌ Team name cannot be empty.", ephemeral=True
        )
    if bot.store.team(team_name):
        return await interaction.response.send_message(
            f"❌ A team named **{team_name}** already exists.", ephemeral=True
        )

    await interaction.response.defer()
    guild = interaction.guild or bot.get_guild(interaction.guild_id)
    if guild is None:
        return await interaction.followup.send(
            "❌ Couldn't read this server yet — restart the bot and try again.", ephemeral=True)
    safe = (team_name.lower().replace(" ", "-") or "team")[:90]

    # 1) Roles
    try:
        team_role = await guild.create_role(
            name=team_role_name(team_name, division),
            color=discord.Color.blue(), mentionable=True, reason="Team creation")
        mgr_role = await league_manager_role(guild, division)
    except discord.Forbidden:
        return await interaction.followup.send(
            "❌ I need the **Manage Roles** permission (and my role must sit above the roles I create).",
            ephemeral=True)
    except discord.HTTPException as exc:
        return await interaction.followup.send(f"❌ Couldn't create the team role ({exc}).", ephemeral=True)

    try:
        await manager.add_roles(team_role, mgr_role, reason="Team creation")
    except discord.HTTPException:
        pass  # role hierarchy — team is still created; assign manually if needed

    # 2) Category + text channel + voice channel
    overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        team_role: discord.PermissionOverwrite(view_channel=True, send_messages=True, connect=True),
        mgr_role: discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_channels=True),
    }
    text = voice = None
    try:
        # Use the server's existing team category for this league; only make one if none exists.
        category = find_team_category(guild, division) or await get_or_create_category(guild, f"{division} Teams")
        text = await guild.create_text_channel(f"{safe}-team-chat", category=category, overwrites=overwrites, reason="Team creation")
        voice = await guild.create_voice_channel(f"{team_name} VC", category=category, overwrites=overwrites, reason="Team creation")
    except discord.Forbidden:
        await interaction.followup.send(
            "⚠️ Team role created, but I need **Manage Channels** to make the text/voice channels.",
            ephemeral=True)
    except discord.HTTPException as exc:
        await interaction.followup.send(f"⚠️ Team role created, but a channel failed ({exc}).", ephemeral=True)

    bot.store.teams[team_name] = {
        "manager": manager.id,
        "division": division,
        "roster": [manager.id],
        "staff": {},
        "has_played_match": False,
        # New teams default their manager to "Playing" (shown on the roster
        # board) unless later toggled off with /set-playing.
        "manager_playing": True,
        "role_id": team_role.id,
        "text_channel_id": text.id if text else None,
        "voice_channel_id": voice.id if voice else None,
        "created": datetime.now(timezone.utc).isoformat(),
    }
    await bot.store.save()
    try:
        await refresh_division_records(guild)
    except Exception:
        log.exception("Board refresh failed after create-team.")

    embed = discord.Embed(title="🏆 Team Created", color=discord.Color.green())
    embed.add_field(name="Team", value=team_name, inline=True)
    embed.add_field(name="League", value=division, inline=True)
    embed.add_field(name="Manager", value=manager.mention, inline=True)
    embed.add_field(name="Role", value=team_role.mention, inline=True)
    embed.add_field(name="Text", value=text.mention if text else "—", inline=True)
    embed.add_field(name="Voice", value=voice.mention if voice else "—", inline=True)
    await interaction.followup.send(embed=embed)


@bot.tree.command(name="delete-team", description="Delete a team (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def delete_team(interaction: discord.Interaction, team: Optional[str] = None) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)

    if team:
        if not bot.store.team(team):
            return await interaction.response.send_message(
                "❌ Unknown team — start typing the name and pick it from the list.", ephemeral=True
            )
        return await interaction.response.send_message(
            f"⚠️ Delete {team_mention(interaction.guild, team)} (**{team}**)? "
            "This removes its channels, role and data.",
            view=ConfirmDeleteView(team),
            ephemeral=True,
        )

    # No team supplied (e.g. an older command definition before a re-sync):
    # show this server's teams so the admin can copy an exact name.
    names = [n for n, t in bot.store.teams.items() if team_in_guild(interaction.guild, n, t)]
    names = sorted(names) or bot.store.team_names()
    if not names:
        return await interaction.response.send_message("No teams found.", ephemeral=True)
    listing = "\n".join(f"• {n}" for n in names)
    await interaction.response.send_message(
        "Run `/delete-team team:<name>` and pick from the autocomplete. Teams in this server:\n"
        f"{listing[:1800]}",
        ephemeral=True,
    )


@bot.tree.command(name="set-team-played", description="Mark whether a team has played an official match (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def set_team_played(interaction: discord.Interaction, team: str, has_played: bool) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    team_data["has_played_match"] = has_played
    await bot.store.save()
    await interaction.response.send_message(
        f"✅ **{team}** marked as {'having played' if has_played else 'not having played'} an official match.",
        ephemeral=True,
    )


@bot.tree.command(name="transfer", description="Move a player from one team to another (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(to_team=team_autocomplete)
async def transfer(interaction: discord.Interaction, player: discord.Member, to_team: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if not bot.store.team(to_team):
        return await interaction.response.send_message(
            f"❌ Team **{to_team}** does not exist.", ephemeral=True
        )
    current = bot.store.find_member_team(player.id)
    if current == to_team:
        return await interaction.response.send_message(
            f"{player.mention} is already on **{to_team}**.", ephemeral=True
        )
    eligibility_error = league_eligibility_error(player, bot.store.team(to_team))
    if eligibility_error:
        return await interaction.response.send_message(f"❌ {eligibility_error}", ephemeral=True)
    if current:
        await remove_player_from_team(player, current)
    success, message = await add_player_to_team(player, to_team, bypass_limits=True)
    if not success:
        return await interaction.response.send_message("❌ " + message, ephemeral=True)
    move = f"{player.mention} transferred to {team_mention(interaction.guild, to_team)}" + (f" from {team_mention(interaction.guild, current)}" if current else "")
    await log_move(interaction.guild, ("transfers", "history"), f"🔁 {move}")
    await interaction.response.send_message("✅ " + move)


@bot.tree.command(name="loan", description="Record a loan deal (Admin only)")
@app_commands.guild_only()
@app_commands.describe(duration="e.g. '1 season', '4 weeks'")
@app_commands.autocomplete(from_team=team_autocomplete, to_team=team_autocomplete)
async def loan(
    interaction: discord.Interaction,
    player: discord.Member,
    from_team: str,
    to_team: str,
    duration: str,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if not bot.store.team(from_team) or not bot.store.team(to_team):
        return await interaction.response.send_message(
            "❌ One of those teams does not exist.", ephemeral=True
        )
    await log_move(
        interaction.guild,
        "loans",
        f"🔄 {player.mention} loaned from **{from_team}** → **{to_team}** ({duration})",
        color=discord.Color.purple(),
    )
    await interaction.response.send_message(
        f"✅ Loan logged: {player.mention} → **{to_team}** ({duration}). "
        "This is a record only — rosters are unchanged; use `/transfer` to move them.",
        ephemeral=True,
    )


async def _change_division(
    interaction: discord.Interaction, team: str, division: str, verb: str
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    old_division = team_data.get("division", "?")
    if old_division == division:
        return await interaction.response.send_message(
            f"**{team}** is already in **{division}**.", ephemeral=True
        )

    await interaction.response.defer()
    guild = interaction.guild
    team_data["division"] = division
    await bot.store.save()

    # Rename the team role to reflect the new division, e.g. "NOMAX Vortex (EL)".
    role = guild.get_role(team_data["role_id"]) if team_data.get("role_id") else None
    if role:
        try:
            await role.edit(name=team_role_name(team, division), reason=f"Team {verb}")
        except discord.HTTPException:
            log.warning("Could not rename role for %s.", team)

    # Move the team's channels into the new division category.
    category = find_team_category(guild, division) or await get_or_create_category(guild, f"{division} Teams")
    for key in ("text_channel_id", "voice_channel_id"):
        channel = guild.get_channel(team_data.get(key)) if team_data.get(key) else None
        if channel:
            try:
                await channel.edit(category=category, reason=f"Team {verb}")
            except discord.HTTPException:
                log.warning("Could not move channel for %s.", team)

    emoji = "⬆️" if verb == "promoted" else "⬇️"
    await log_move(
        guild,
        "promotion",
        f"{emoji} {team_mention(interaction.guild, team)} {verb}: **{old_division}** → **{division}**",
        color=discord.Color.green() if verb == "promoted" else discord.Color.red(),
    )
    await interaction.followup.send(f"✅ {team_mention(interaction.guild, team)} {verb} to **{division}**.")


@bot.tree.command(name="promote", description="Promote a team to a higher division (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.autocomplete(division=division_autocomplete)
async def promote(interaction: discord.Interaction, team: str, division: str) -> None:
    await _change_division(interaction, team, division, "promoted")


@bot.tree.command(name="relegate", description="Relegate a team to a lower division (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.autocomplete(division=division_autocomplete)
async def relegate(interaction: discord.Interaction, team: str, division: str) -> None:
    await _change_division(interaction, team, division, "relegated")


@bot.tree.command(name="close-transfer-window", description="Close the transfer window (Admin only)")
@app_commands.guild_only()
async def close_transfer_window(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    bot.store.data["settings"]["transfer_window_open"] = False
    await bot.store.save()
    await log_move(
        interaction.guild, "window", "🔒 **The transfer window is now CLOSED.**",
        color=discord.Color.red(),
    )
    try:
        await refresh_division_records(interaction.guild)
    except Exception:
        log.exception("Board refresh failed after closing window.")
    await interaction.response.send_message(
        "✅ Transfer window closed. `/join` and `/sign` are now blocked for non-admins.",
        ephemeral=True,
    )


@bot.tree.command(name="open-transfer-window", description="Re-open the transfer window (Admin only)")
@app_commands.guild_only()
async def open_transfer_window(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    bot.store.data["settings"]["transfer_window_open"] = True
    await bot.store.save()
    await log_move(
        interaction.guild, "window", "🟢 **The transfer window is now OPEN.**",
        color=discord.Color.green(),
    )
    try:
        await refresh_division_records(interaction.guild)
    except Exception:
        log.exception("Board refresh failed after opening window.")
    await interaction.response.send_message("✅ Transfer window opened.", ephemeral=True)


@bot.tree.command(name="set-manager", description="Change a team's manager (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def set_manager(interaction: discord.Interaction, team: str, manager: discord.Member) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    old_manager_id = team_data.get("manager")
    team_data["manager"] = manager.id
    if manager.id not in team_data.setdefault("roster", []):
        team_data["roster"].append(manager.id)
    await bot.store.save()

    await add_team_role(manager, team)
    mgr_role = await get_or_create_role(
        interaction.guild, f"👔 Team Manager ({team_data.get('division')})", color=discord.Color.gold()
    )
    try:
        await manager.add_roles(mgr_role, reason="Set as team manager")
    except discord.HTTPException:
        pass

    previous = f"<@{old_manager_id}>" if old_manager_id else "*nobody*"
    await log_move(
        interaction.guild,
        "managerial",
        f"👔 {team_mention(interaction.guild, team)} manager changed: {previous} → {manager.mention}",
        color=discord.Color.gold(),
    )
    await interaction.response.send_message(f"✅ {manager.mention} is now the manager of {team_mention(interaction.guild, team)}.")


@bot.tree.command(name="rename-team", description="Rename a team, its role and channels (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def rename_team(interaction: discord.Interaction, team: str, new_name: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    new_name = new_name.strip()
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    if not new_name:
        return await interaction.response.send_message("❌ New name cannot be empty.", ephemeral=True)
    if bot.store.team(new_name):
        return await interaction.response.send_message(
            f"❌ A team named **{new_name}** already exists.", ephemeral=True
        )

    await interaction.response.defer()
    guild = interaction.guild
    safe = new_name.lower().replace(" ", "-")

    role = (
        guild.get_role(team_data["role_id"])
        if team_data.get("role_id")
        else discord.utils.get(guild.roles, name=team)
    )
    if role:
        try:
            await role.edit(
                name=team_role_name(new_name, team_data.get("division", "?")), reason="Team renamed"
            )
        except discord.HTTPException:
            log.warning("Could not rename role for %s.", team)
    for key, suffix in (("text_channel_id", "-talking"), ("voice_channel_id", "-vc")):
        channel = guild.get_channel(team_data.get(key)) if team_data.get(key) else None
        if channel:
            try:
                await channel.edit(name=f"{safe}{suffix}", reason="Team renamed")
            except discord.HTTPException:
                log.warning("Could not rename channel for %s.", team)

    bot.store.teams[new_name] = bot.store.teams.pop(team)
    await bot.store.save()
    await interaction.followup.send(f"✅ **{team}** renamed to **{new_name}**.")


@bot.tree.command(name="edit-team", description="Edit a team's name and details (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.describe(
    team="Team to edit",
    new_name="New team name (optional)",
    description="Short description / tagline shown on team-info (optional; blank to clear)",
    logo="Logo image URL shown on team-info (optional; blank to clear)",
)
async def edit_team(
    interaction: discord.Interaction,
    team: str,
    new_name: Optional[str] = None,
    description: Optional[str] = None,
    logo: Optional[str] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    if new_name is None and description is None and logo is None:
        return await interaction.response.send_message(
            "❌ Give me at least one thing to change: `new_name`, `description`, and/or `logo`.",
            ephemeral=True,
        )

    await interaction.response.defer()
    guild = interaction.guild
    changes: list[str] = []

    # --- details (mutating team_data persists; it's the live stored dict) ---
    if description is not None:
        description = description.strip()
        if description:
            team_data["description"] = description
            changes.append("description updated")
        else:
            team_data.pop("description", None)
            changes.append("description cleared")
    if logo is not None:
        logo = logo.strip()
        if logo:
            team_data["logo"] = logo
            changes.append("logo updated")
        else:
            team_data.pop("logo", None)
            changes.append("logo cleared")

    # --- name last: it migrates the storage key (teams are keyed by name) ---
    current_name = team
    if new_name is not None:
        new_name = new_name.strip()
        if not new_name:
            return await interaction.followup.send("❌ New name cannot be empty.")
        if new_name != team and bot.store.team(new_name):
            return await interaction.followup.send(f"❌ A team named **{new_name}** already exists.")
        if new_name != team:
            safe = new_name.lower().replace(" ", "-")
            role = (
                guild.get_role(team_data["role_id"])
                if team_data.get("role_id")
                else discord.utils.get(guild.roles, name=team)
            )
            if role:
                try:
                    await role.edit(
                        name=team_role_name(new_name, team_data.get("division", "?")),
                        reason="Team edited",
                    )
                except discord.HTTPException:
                    log.warning("Could not rename role for %s.", team)
            for key, suffix in (("text_channel_id", "-talking"), ("voice_channel_id", "-vc")):
                channel = guild.get_channel(team_data.get(key)) if team_data.get(key) else None
                if channel:
                    try:
                        await channel.edit(name=f"{safe}{suffix}", reason="Team edited")
                    except discord.HTTPException:
                        log.warning("Could not rename channel for %s.", team)
            bot.store.teams[new_name] = bot.store.teams.pop(team)
            changes.append(f"name → **{new_name}**")
            current_name = new_name

    await bot.store.save()

    embed = discord.Embed(
        title=f"✏️ Team Updated — {current_name}",
        description="\n".join(f"• {c}" for c in changes) or "No changes made.",
        color=discord.Color.green(),
    )
    if team_data.get("logo"):
        embed.set_thumbnail(url=team_data["logo"])
    await interaction.followup.send(embed=embed)


@bot.tree.command(name="set-playing", description="Mark your team's manager as playing or non-playing")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.describe(
    playing="True if the manager is an active player on the team",
    team="(Admin) which team — defaults to your own",
)
async def set_playing(interaction: discord.Interaction, playing: bool, team: Optional[str] = None) -> None:
    if team:
        if not is_admin(interaction):
            return await interaction.response.send_message(
                "❌ Only an admin can set another team. Leave `team` blank to set your own.", ephemeral=True
            )
        team_name = team
        team_data = bot.store.team(team_name)
        if not team_data:
            return await interaction.response.send_message(
                f"❌ Team **{team_name}** does not exist.", ephemeral=True
            )
    else:
        team_name = bot.store.find_member_team(interaction.user.id)
        if not team_name:
            return await interaction.response.send_message("❌ You are not on a team.", ephemeral=True)
        team_data = bot.store.team(team_name)
        if team_data.get("manager") != interaction.user.id and not is_admin(interaction):
            return await interaction.response.send_message(
                "❌ Only that team's manager (or an admin) can set this.", ephemeral=True
            )
    team_data["manager_playing"] = bool(playing)
    await bot.store.save()
    try:
        await refresh_division_records(interaction.guild)
    except Exception:
        log.exception("Board refresh failed after set-playing.")
    await interaction.response.send_message(
        f"✅ **{team_name}** manager marked as **{'Playing' if playing else 'Not Playing'}**.",
        ephemeral=True,
    )

@bot.tree.command(name="join", description="Request to join a team")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def join(interaction: discord.Interaction, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    if not bot.store.window_open and not is_admin(interaction):
        return await interaction.response.send_message(
            "🔒 The transfer window is closed.", ephemeral=True
        )
    eligibility_error = league_eligibility_error(interaction.user, team_data)
    if eligibility_error:
        return await interaction.response.send_message(f"❌ {eligibility_error}", ephemeral=True)
    current = bot.store.find_member_team(interaction.user.id)
    if current:
        return await interaction.response.send_message(
            f"❌ You're already on **{current}**. Use `/leave` first.", ephemeral=True
        )

    manager_id = team_data.get("manager")
    if not manager_id:
        return await interaction.response.send_message(
            "❌ This team has no manager set.", ephemeral=True
        )
    try:
        manager = await interaction.guild.fetch_member(manager_id)
    except discord.NotFound:
        return await interaction.response.send_message(
            "❌ The team manager is no longer in the server.", ephemeral=True
        )

    try:
        await manager.send(
            f"📨 **Join Request**\n{interaction.user.mention} wants to join **{team}**.",
            view=JoinRequestView(interaction.user, team),
        )
    except discord.Forbidden:
        return await interaction.response.send_message(
            "❌ The manager has DMs disabled — ask an admin to add you directly.", ephemeral=True
        )
    except discord.HTTPException:
        return await interaction.response.send_message(
            "❌ I couldn't deliver the join request to the manager's DMs. Please try again later.", ephemeral=True
        )
    await interaction.response.send_message(
        f"✅ Request sent to the manager of **{team}**.", ephemeral=True
    )


@bot.tree.command(name="sign", description="Offer a player a spot (player accepts, then staff confirm)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def sign(interaction: discord.Interaction, player: discord.Member, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    if interaction.user.id != team_data.get("manager") and not is_admin(interaction):
        return await interaction.response.send_message(
            "❌ Only the team manager or an admin can sign players.", ephemeral=True
        )
    if not bot.store.window_open and not is_admin(interaction):
        return await interaction.response.send_message(
            "🔒 The transfer window is closed.", ephemeral=True
        )
    eligibility_error = league_eligibility_error(player, team_data)
    if eligibility_error:
        return await interaction.response.send_message(f"❌ {eligibility_error}", ephemeral=True)
    current = bot.store.find_member_team(player.id)
    if current:
        return await interaction.response.send_message(
            f"❌ {player.mention} is already on **{current}**.", ephemeral=True
        )

    try:
        await player.send(
            f"✅ **Team Offer**\nYou've been offered a spot on **{team}** by {interaction.user.mention}.",
            view=SignOfferView(
                player, team, interaction.user, interaction.channel_id,
                bypass_window=is_admin(interaction),
            ),
        )
    except discord.Forbidden:
        return await interaction.response.send_message(
            f"❌ {player.mention} has DMs disabled.", ephemeral=True
        )
    except discord.HTTPException:
        return await interaction.response.send_message(
            f"❌ I couldn't deliver the offer to {player.mention}'s DMs. Please try again later.", ephemeral=True
        )
    await interaction.response.send_message(f"✅ Offer sent to {player.mention}.", ephemeral=True)


# --------------------------------------------------------------------------- #
# Roster management
# --------------------------------------------------------------------------- #

@bot.tree.command(name="team_add_player", description="Add a player to a roster (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_add_player(interaction: discord.Interaction, player: discord.Member, team: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    success, message = await add_player_to_team(player, team, bypass_limits=True)
    if success:
        await log_move(interaction.guild, ("transfers", "signings"), f"📥 {message}",
                       color=discord.Color.green())
    await interaction.response.send_message(
        ("✅ " if success else "❌ ") + message, ephemeral=not success
    )


@bot.tree.command(name="team_view_roster", description="View a team's roster")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_view_roster(interaction: discord.Interaction, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    roster = team_data.get("roster", [])
    manager_id = team_data.get("manager")
    lines = [f"<@{uid}>" + (" 👔" if uid == manager_id else "") for uid in roster]
    embed = discord.Embed(
        title=f"📋 Roster — {team}",
        description="\n".join(lines) or "*Empty*",
        color=discord.Color.blue(),
    )
    embed.set_footer(text=f"{len(roster)} player(s) · Division {team_data.get('division', 'N/A')}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="list-teams", description="List all teams grouped by division")
@app_commands.guild_only()
async def list_teams(interaction: discord.Interaction) -> None:
    teams = bot.store.teams
    if not teams:
        return await interaction.response.send_message("No teams exist yet.", ephemeral=True)
    grouped: dict[str, list[tuple[str, int]]] = {}
    for name, team in teams.items():
        grouped.setdefault(team.get("division", "?"), []).append((name, len(team.get("roster", []))))

    _ln = bot.store.settings.get("league_name", "The Titan Elite Division")
    embed = discord.Embed(title=f"🏆 {_ln} Teams", color=discord.Color.blue())
    ordering = DIVISIONS + sorted(set(grouped) - set(DIVISIONS))
    for division in ordering:
        if division in grouped:
            lines = [f"**{name}** — {count} player(s)" for name, count in sorted(grouped[division])]
            embed.add_field(name=division, value="\n".join(lines), inline=False)
    embed.set_footer(text=f"{len(teams)} team(s) total")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="team-info", description="View detailed information about a team")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_info(interaction: discord.Interaction, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    roster = team_data.get("roster", [])
    manager_id = team_data.get("manager")

    embed = discord.Embed(
        title=f"🏆 {team}",
        description=team_data.get("description") or None,
        color=discord.Color.blue(),
    )
    if team_data.get("logo"):
        embed.set_thumbnail(url=team_data["logo"])
    division = team_data.get("division")
    embed.add_field(
        name="League",
        value=f"{league_display_name(division)} · {format_label(division)}" if division else "N/A",
        inline=True,
    )
    embed.add_field(name="Manager", value=f"<@{manager_id}>" if manager_id else "*Vacant*", inline=True)
    embed.add_field(
        name="Played official match",
        value="Yes" if team_data.get("has_played_match") else "No",
        inline=True,
    )
    roster_lines = [f"<@{uid}>" + (" 👔" if uid == manager_id else "") for uid in roster]
    embed.add_field(name=f"Roster ({len(roster)})", value="\n".join(roster_lines) or "*Empty*", inline=False)

    staff_lines = [
        f"**{position}:** " + ", ".join(f"<@{uid}>" for uid in members)
        for position, members in team_data.get("staff", {}).items()
        if members
    ]
    if staff_lines:
        embed.add_field(name="Staff", value="\n".join(staff_lines), inline=False)
    if team_data.get("created"):
        embed.set_footer(text=f"Created {team_data['created'][:10]}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="leave", description="Leave your team")
@app_commands.guild_only()
async def leave(interaction: discord.Interaction) -> None:
    member = interaction.user
    team_name = bot.store.find_member_team(member.id)
    if not team_name:
        return await interaction.response.send_message("You are not on any team.", ephemeral=True)
    was_manager = bot.store.team(team_name).get("manager") == member.id
    await remove_player_from_team(member, team_name)
    role = await assign_free_agent_role(member, team_name)
    await log_move(member.guild, "transfers", f"📤 {member.mention} left **{team_name}**")
    if was_manager:
        await log_move(
            member.guild,
            "managerial",
            f"👔 {member.mention} stepped down as manager of **{team_name}** (left the team)",
            color=discord.Color.gold(),
        )
    await interaction.response.send_message(
        f"✅ You left **{team_name}** and received the **{role}** role."
    )


@bot.tree.command(name="team_kick_player", description="Kick a player from a team (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_kick_player(interaction: discord.Interaction, player: discord.Member, team: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if not await remove_player_from_team(player, team):
        return await interaction.response.send_message(
            "That player is not on that team.", ephemeral=True
        )
    role = await assign_free_agent_role(player, team)
    await log_move(
        interaction.guild, "released", f"👋 {player.mention} was kicked from **{team}**",
        color=discord.Color.orange(),
    )
    await interaction.response.send_message(
        f"✅ {player.mention} kicked from **{team}** — now **{role}**."
    )


@bot.tree.command(name="release_player", description="Release a player (manager or admin)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def release_player(interaction: discord.Interaction, member: discord.Member, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    if interaction.user.id != team_data.get("manager") and not is_admin(interaction):
        return await interaction.response.send_message(
            "❌ Only the team manager or an admin can release players.", ephemeral=True
        )
    if not await remove_player_from_team(member, team):
        return await interaction.response.send_message(
            "That player is not on that team.", ephemeral=True
        )
    role = await assign_free_agent_role(member, team)
    await log_move(
        interaction.guild, "released", f"👋 {member.mention} was released from **{team}**",
        color=discord.Color.orange(),
    )
    await interaction.response.send_message(
        f"✅ {member.mention} released from **{team}** — now **{role}**."
    )


# --------------------------------------------------------------------------- #
# Staff management
# --------------------------------------------------------------------------- #

@bot.tree.command(name="add_staff", description="Add non-playing staff to a team (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.choices(position=[app_commands.Choice(name=p, value=p) for p in STAFF_POSITIONS])
async def add_staff(
    interaction: discord.Interaction,
    member: discord.Member,
    team: str,
    position: app_commands.Choice[str],
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    staff = team_data.setdefault("staff", {}).setdefault(position.value, [])
    if member.id in staff:
        return await interaction.response.send_message(
            f"{member.mention} is already **{position.value}** for **{team}**.", ephemeral=True
        )
    staff.append(member.id)
    await bot.store.save()
    await interaction.response.send_message(
        f"✅ {member.mention} added as **{position.value}** to **{team}**."
    )


@bot.tree.command(name="remove_staff", description="Remove a staff member from a team (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def remove_staff(interaction: discord.Interaction, member: discord.Member, team: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    removed_from = []
    for position, members in team_data.get("staff", {}).items():
        if member.id in members:
            members.remove(member.id)
            removed_from.append(position)
    if not removed_from:
        return await interaction.response.send_message(
            f"{member.mention} is not staff for **{team}**.", ephemeral=True
        )
    await bot.store.save()
    await interaction.response.send_message(
        f"✅ Removed {member.mention} as {', '.join(removed_from)} from **{team}**."
    )


@bot.tree.command(name="team_staff", description="View all staff of a team")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_staff(interaction: discord.Interaction, team: str) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(
            f"❌ Team **{team}** does not exist.", ephemeral=True
        )
    embed = discord.Embed(title=f"Staff — {team}", color=discord.Color.blue())
    for position, members in team_data.get("staff", {}).items():
        if members:
            embed.add_field(
                name=position, value=", ".join(f"<@{uid}>" for uid in members), inline=False
            )
    if not embed.fields:
        embed.description = "No staff members."
    await interaction.response.send_message(embed=embed)


# --------------------------------------------------------------------------- #
# Player commands
# --------------------------------------------------------------------------- #

@bot.tree.command(name="link-epic", description="Link your Epic Games ID to your profile")
@app_commands.guild_only()
async def link_epic(interaction: discord.Interaction, epic_id: str) -> None:
    epic_id = epic_id.strip()
    bot.store.players.setdefault(str(interaction.user.id), {})["epic"] = epic_id
    await bot.store.save()
    await interaction.response.send_message(f"✅ Linked Epic ID: **{epic_id}**", ephemeral=True)


@bot.tree.command(name="set-rank", description="Set your rank or MMR (shown in free-agent posts)")
@app_commands.guild_only()
@app_commands.describe(
    rank="A rank, or MMR such as '1650 MMR (3v3)' or '1450 MMR (2v2)'",
    division="Which division's managers should be pinged when you're a free agent",
    member="(Admin) set someone else's rank",
)
@app_commands.autocomplete(division=division_autocomplete)
async def set_rank(
    interaction: discord.Interaction,
    rank: str,
    division: Optional[str] = None,
    member: Optional[discord.Member] = None,
) -> None:
    target = interaction.user
    if member and member.id != interaction.user.id:
        if not is_admin(interaction):
            return await interaction.response.send_message(
                "❌ Only admins can set someone else's rank.", ephemeral=True
            )
        target = member
    pdata = bot.store.players.setdefault(str(target.id), {})
    rank_value = rank.strip()
    mmr_match = re.fullmatch(r"(\d{1,4})\s*MMR\s*\((2v2|3v3)\)", rank_value, re.IGNORECASE)
    if mmr_match:
        mmr_value = int(mmr_match.group(1))
        if mmr_value > 5000:
            return await interaction.response.send_message("❌ Enter an MMR from 0 to 5000.", ephemeral=True)
        playlist_value = mmr_match.group(2).lower()
        pdata["mmr"] = mmr_value
        pdata["playlist"] = playlist_value
        rank_value = f"{mmr_value} MMR ({playlist_value})"
    else:
        pdata.pop("mmr", None)
        pdata.pop("playlist", None)
    pdata["rank"] = rank_value
    resolved_division = division or league_for_player(pdata)
    if resolved_division:
        pdata["last_division"] = resolved_division
    else:
        pdata.pop("last_division", None)
    await bot.store.save()
    extra = f" · free-agent league **{resolved_division}**" if resolved_division else " · below current league bands"
    await interaction.response.send_message(
        f"✅ Rank for {target.mention} set to **{rank_value}**{extra}.", ephemeral=True
    )


@bot.tree.command(name="set-rl-name", description="Set your Rocket League username (shown on X League rosters)")
@app_commands.guild_only()
@app_commands.describe(name="Your Rocket League in-game name", member="(Admin) set someone else's")
async def set_rl_name(interaction: discord.Interaction, name: str, member: Optional[discord.Member] = None) -> None:
    target = interaction.user
    if member and member.id != interaction.user.id:
        if not is_admin(interaction):
            return await interaction.response.send_message("❌ Only admins can set someone else's RL name.", ephemeral=True)
        target = member
    pdata = bot.store.players.setdefault(str(target.id), {})
    pdata["rl_name"] = name.strip()
    await bot.store.save()
    try:
        await refresh_division_records(interaction.guild)
    except Exception:
        log.exception("Board refresh failed after set-rl-name.")
    await interaction.response.send_message(
        f"✅ Rocket League name for {target.mention} set to **{name.strip()}**.", ephemeral=True)


@bot.tree.command(name="add-co-manager", description="Add a co-manager to a team (manager or admin)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def add_co_manager(interaction: discord.Interaction, team: str, player: discord.Member) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(f"❌ Team **{team}** does not exist.", ephemeral=True)
    if interaction.user.id != team_data.get("manager") and not is_admin(interaction):
        return await interaction.response.send_message("❌ Only the team manager or an admin can do this.", ephemeral=True)
    staff = team_data.setdefault("staff", {})
    co = staff.setdefault("Co-Manager", [])
    if player.id in co:
        return await interaction.response.send_message(f"❌ {player.mention} is already a co-manager.", ephemeral=True)
    co.append(player.id)
    # give the league's co-manager role if it's configured
    cfg = league_cfg(team_data.get("division"))
    role = interaction.guild.get_role(cfg.get("co_manager_role")) if cfg.get("co_manager_role") else None
    if role:
        try:
            await player.add_roles(role, reason="Co-manager")
        except discord.HTTPException:
            pass
    await bot.store.save()
    await refresh_division_records(interaction.guild)
    await interaction.response.send_message(f"✅ {player.mention} is now a co-manager of **{team}**.")


@bot.tree.command(name="remove-co-manager", description="Remove a co-manager from a team (manager or admin)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def remove_co_manager(interaction: discord.Interaction, team: str, player: discord.Member) -> None:
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(f"❌ Team **{team}** does not exist.", ephemeral=True)
    if interaction.user.id != team_data.get("manager") and not is_admin(interaction):
        return await interaction.response.send_message("❌ Only the team manager or an admin can do this.", ephemeral=True)
    co = team_data.get("staff", {}).get("Co-Manager", [])
    if player.id not in co:
        return await interaction.response.send_message(f"❌ {player.mention} isn't a co-manager of **{team}**.", ephemeral=True)
    co.remove(player.id)
    if not co:
        team_data["staff"].pop("Co-Manager", None)
    cfg = league_cfg(team_data.get("division"))
    role = interaction.guild.get_role(cfg.get("co_manager_role")) if cfg.get("co_manager_role") else None
    if role and role in player.roles:
        try:
            await player.remove_roles(role, reason="Co-manager removed")
        except discord.HTTPException:
            pass
    await bot.store.save()
    await refresh_division_records(interaction.guild)
    await interaction.response.send_message(f"✅ Removed {player.mention} as co-manager of **{team}**.")


@bot.tree.command(name="profile", description="View a player's profile")
@app_commands.guild_only()
async def profile(interaction: discord.Interaction, user: Optional[discord.Member] = None) -> None:
    user = user or interaction.user
    pdata = bot.store.players.get(str(user.id), {})
    team_name = bot.store.find_member_team(user.id)

    embed = discord.Embed(title=f"Profile — {user.display_name}", color=discord.Color.blue())
    embed.set_thumbnail(url=user.display_avatar.url)
    embed.add_field(name="Epic ID", value=pdata.get("epic", "Not linked"), inline=False)
    tracker_link = pdata.get("tracker_link")
    embed.add_field(
        name="Tracker profile",
        value=f"[Open Tracker profile]({tracker_link})" if tracker_link and is_tracker_profile_link(tracker_link) else "Not linked",
        inline=False,
    )
    embed.add_field(name="Rank", value=pdata.get("rank", "Not set"), inline=True)
    if pdata.get("mmr") is not None and pdata.get("playlist") in {"2v2", "3v3"}:
        embed.add_field(name="Playlist / MMR", value=f"{pdata['playlist']} · {pdata['mmr']} MMR", inline=True)
        embed.add_field(name="MMR league", value=league_display_name(league_for_player(pdata)), inline=True)
    verify_status = pdata.get("verification_status") or ("approved" if pdata.get("verified") else "not submitted")
    embed.add_field(name="Verification", value=verify_status.replace("_", " ").title(), inline=True)
    embed.add_field(name="Team", value=team_name or "Free agent", inline=True)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="myteam", description="Check which team you are on")
@app_commands.guild_only()
async def myteam(interaction: discord.Interaction) -> None:
    team_name = bot.store.find_member_team(interaction.user.id)
    if not team_name:
        return await interaction.response.send_message("You are not on any team.", ephemeral=True)
    team_data = bot.store.team(team_name)
    embed = discord.Embed(title=f"Your Team: {team_name}", color=discord.Color.green())
    embed.add_field(name="Division", value=team_data.get("division", "N/A"), inline=True)
    embed.add_field(name="Manager", value=f"<@{team_data.get('manager')}>", inline=True)
    embed.add_field(name="Roster size", value=str(len(team_data.get("roster", []))), inline=True)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="freeagents", description="List current free agents")
@app_commands.guild_only()
async def freeagents(interaction: discord.Interaction) -> None:
    guild = interaction.guild
    embed = discord.Embed(title="📋 Free Agents", color=discord.Color.green())
    agents = collect_free_agents(guild)
    for role_name, restricted in ((FREE_AGENT_ROLE, False), (RESTRICTED_FREE_AGENT_ROLE, True)):
        members = [(member, free_agent_division(member, bot.store.players.get(str(member.id), {})))
                   for member, is_restricted in agents if is_restricted == restricted]
        value = "\n".join(
            f"{member.mention} — **{league_display_name(division)}** · {format_label(division)}"
            for member, division in members
        ) if members else "*None*"
        embed.add_field(name=f"{role_name} ({len(members)})", value=value, inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="standings", description="View the league standings for a division")
@app_commands.guild_only()
@app_commands.autocomplete(division=division_autocomplete)
async def standings(interaction: discord.Interaction, division: str) -> None:
    rows = compute_standings(interaction.guild, division)
    if not rows:
        return await interaction.response.send_message(
            f"No teams in **{division}** yet.", ephemeral=True
        )
    league = bot.store.settings.get("league_name", "The Titan Elite Division")
    embed = discord.Embed(
        title=f"🏅 {league} — {division} Standings",
        description=format_standings_table(rows),
        color=discord.Color.gold(),
    )
    embed.set_footer(text=f"Season {bot.store.season} · P=played W=won L=lost GD=game diff Pts=points")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="leaderboard", description="Top teams by record — one league or overall")
@app_commands.guild_only()
@app_commands.describe(division="Limit to one league (leave blank for overall)", top="How many to show (default 10)")
@app_commands.autocomplete(division=division_autocomplete)
async def leaderboard(
    interaction: discord.Interaction,
    division: Optional[str] = None,
    top: Optional[int] = 10,
) -> None:
    top = max(1, min(25, top or 10))
    league = bot.store.settings.get("league_name", "The Titan Elite Division")

    if division:
        rows = [dict(r, division=division) for r in compute_standings(interaction.guild, division)]
        title = f"🏆 {division} League Leaderboard"
    else:
        rows = []
        for d in DIVISIONS:
            rows.extend(dict(r, division=d) for r in compute_standings(interaction.guild, d))
        rows.sort(key=lambda r: (r["Pts"], r["GF"] - r["GA"], r["GF"], r["W"]), reverse=True)
        title = f"🏆 {league} — Overall Leaderboard"

    # Prefer teams that have actually played; if none have, show the seeded list.
    played = [r for r in rows if r["P"] > 0]
    rows = (played or rows)[:top]
    if not rows:
        return await interaction.response.send_message("No teams to rank yet.", ephemeral=True)

    medals = {1: "🥇", 2: "🥈", 3: "🥉"}
    lines = []
    for i, r in enumerate(rows, 1):
        rank = medals.get(i, f"`#{i:>2}`")
        div = f" · {r['division']}" if not division else ""
        gd = r["GF"] - r["GA"]
        lines.append(f"{rank} **{r['team']}**{div} — {r['W']}W-{r['L']}L · GD {gd:+d} · **{r['Pts']} pts**")

    embed = discord.Embed(title=title, description="\n".join(lines), color=discord.Color.gold())
    embed.set_footer(text=f"Season {bot.store.season} · ranked by points, then game difference")
    await interaction.response.send_message(embed=embed)


# --------------------------------------------------------------------------- #
# Match / competition commands
# --------------------------------------------------------------------------- #

def _is_team_staff(interaction: discord.Interaction, team_name: str) -> bool:
    """True if the user is the manager (or any staff) of the team, or an admin."""
    if is_admin(interaction):
        return True
    team = bot.store.team(team_name) or {}
    if interaction.user.id == team.get("manager"):
        return True
    for members in team.get("staff", {}).values():
        if interaction.user.id in members:
            return True
    return False


class ScheduleKickoffModal(ui.Modal, title="Fixture kickoff"):
    kickoff = ui.TextInput(label="Kickoff UTC", placeholder="2026-08-08 21:00", max_length=16)
    def __init__(self, wizard: "ScheduleWizard") -> None:
        super().__init__(); self.wizard = wizard
    async def on_submit(self, interaction: discord.Interaction) -> None:
        await schedule.callback(interaction, self.wizard.team1, self.wizard.team2, self.kickoff.value)


class ScheduleWizard(ui.View):
    """Step-by-step team selection for `/schedule` with no arguments."""
    def __init__(self, owner_id: int) -> None:
        super().__init__(timeout=300); self.owner_id = owner_id; self.team1: Optional[str] = None; self.team2: Optional[str] = None
        self._home_step()
    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id == self.owner_id or is_admin(interaction): return True
        await interaction.response.send_message("Only the person who opened this scheduler can use it.", ephemeral=True); return False
    def _home_step(self) -> None:
        choices = [discord.SelectOption(label=name, value=name) for name in bot.store.team_names()[:25]]
        select = ui.Select(placeholder="Step 1 — Select home team", options=choices or [discord.SelectOption(label="No teams registered", value="none")], disabled=not choices)
        async def chosen(interaction: discord.Interaction) -> None:
            self.team1 = select.values[0]; self.clear_items(); self._away_step()
            await interaction.response.edit_message(content="Step 2 — Select away team.", view=self)
        select.callback = chosen; self.add_item(select)
    def _away_step(self) -> None:
        choices = [discord.SelectOption(label=name, value=name) for name in bot.store.team_names() if name != self.team1][:25]
        select = ui.Select(placeholder="Step 2 — Select away team", options=choices)
        async def chosen(interaction: discord.Interaction) -> None:
            self.team2 = select.values[0]; self.clear_items(); button = ui.Button(label="Enter kickoff", style=discord.ButtonStyle.primary)
            async def modal_click(button_interaction: discord.Interaction) -> None: await button_interaction.response.send_modal(ScheduleKickoffModal(self))
            button.callback = modal_click; self.add_item(button)
            await interaction.response.edit_message(content="Step 3 — Enter kickoff date and time in UTC.", view=self)
        select.callback = chosen; self.add_item(select)


class FixtureConfirmationView(ui.View):
    """Persistent manager controls for a scheduled fixture."""
    def __init__(self, match_id: str) -> None:
        super().__init__(timeout=None)
        self.match_id = match_id
        for child in self.children:
            child.custom_id = f"ecrl-fixture:{match_id}:{child.custom_id}"

    async def _team_for(self, interaction: discord.Interaction) -> Optional[str]:
        match = bot.store.matches.get(self.match_id)
        if not match or match.get("guild_id") != interaction.guild_id:
            await interaction.response.send_message("This fixture no longer exists.", ephemeral=True)
            return None
        for name in (match["team1"], match["team2"]):
            if _is_team_staff(interaction, name):
                return name
        await interaction.response.send_message("Only a manager or co-manager of either team can use this.", ephemeral=True)
        return None

    @ui.button(label="Confirm", emoji="✅", style=discord.ButtonStyle.success, custom_id="confirm")
    async def confirm(self, interaction: discord.Interaction, _: ui.Button) -> None:
        team = await self._team_for(interaction)
        if not team:
            return
        match = bot.store.matches[self.match_id]
        confirmations = set(match.get("confirmations", [])); confirmations.add(team)
        match["confirmations"] = sorted(confirmations)
        match["fixture_status"] = "Confirmed" if {match["team1"], match["team2"]}.issubset(confirmations) else "Awaiting Confirmation"
        await bot.store.save()
        await interaction.response.edit_message(embed=fixture_embed(interaction.guild, match), view=self)

    @ui.button(label="Can't Play", emoji="❌", style=discord.ButtonStyle.danger, custom_id="unavailable")
    async def unavailable(self, interaction: discord.Interaction, _: ui.Button) -> None:
        team = await self._team_for(interaction)
        if not team:
            return
        match = bot.store.matches[self.match_id]
        match["fixture_status"] = "Under Review"; match["unavailable_team"] = team
        await bot.store.save()
        await interaction.response.edit_message(embed=fixture_embed(interaction.guild, match), view=self)

    @ui.button(label="Request Reschedule", style=discord.ButtonStyle.secondary, custom_id="reschedule")
    async def reschedule(self, interaction: discord.Interaction, _: ui.Button) -> None:
        team = await self._team_for(interaction)
        if team:
            await interaction.response.send_modal(RescheduleRequestModal(self.match_id, team))


class RescheduleRequestModal(ui.Modal, title="Request a fixture reschedule"):
    proposal = ui.TextInput(label="Proposed date/time (UTC)", placeholder="2026-08-08 21:00")
    reason = ui.TextInput(label="Reason", style=discord.TextStyle.paragraph, max_length=500)
    def __init__(self, match_id: str, team: str) -> None:
        super().__init__(); self.match_id, self.team = match_id, team
    async def on_submit(self, interaction: discord.Interaction) -> None:
        match = bot.store.matches.get(self.match_id)
        if not match: return await interaction.response.send_message("Fixture not found.", ephemeral=True)
        match.setdefault("reschedule_requests", []).append({"team": self.team, "by": interaction.user.id, "proposal": self.proposal.value, "reason": self.reason.value})
        match["fixture_status"] = "Under Review"
        await bot.store.save()
        await interaction.response.send_message("Reschedule request submitted to league staff.", ephemeral=True)


def fixture_embed(guild: discord.Guild, match: dict[str, Any]) -> discord.Embed:
    when = (match.get("scheduled_for") or "TBC").replace("T", " ")[:16]
    embed = discord.Embed(title=f"{match.get('division', 'The Titan Elites Division')} | GAME WEEK {match.get('matchweek') or 'TBC'}", color=discord.Color.blurple())
    embed.description = f"## {team_mention(guild, match['team1'])}  VS  {team_mention(guild, match['team2'])}\n\n**{when} UTC**"
    embed.add_field(name="Status", value=match.get("fixture_status", "Awaiting Confirmation"), inline=False)
    embed.set_footer(text=f"Match {match['id']}")
    return embed


async def create_private_match_channel(guild: discord.Guild, match: dict[str, Any]) -> Optional[discord.TextChannel]:
    category_id = bot.store.settings.get("match_channel_category_id")
    category = guild.get_channel(category_id) if category_id else None
    if not isinstance(category, discord.CategoryChannel): return None
    overwrites: dict[Any, discord.PermissionOverwrite] = {guild.default_role: discord.PermissionOverwrite(view_channel=False)}
    for name in (match["team1"], match["team2"]):
        team = bot.store.team(name) or {}
        if team.get("role_id") and (role := guild.get_role(team["role_id"])): overwrites[role] = discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True)
        for member_id in [team.get("manager")] + [uid for ids in team.get("staff", {}).values() for uid in ids]:
            if member_id and (member := guild.get_member(member_id)): overwrites[member] = discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True)
    if guild.me: overwrites[guild.me] = discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_channels=True)
    slug = re.sub(r"[^a-z0-9-]+", "-", f"{match['team1']}-vs-{match['team2']}".lower()).strip("-")[:90]
    channel = await guild.create_text_channel(slug, category=category, overwrites=overwrites, reason="ECRL fixture channel")
    await channel.send(f"Private match room: **{match['team1']} vs {match['team2']}**.")
    return channel


@bot.tree.command(name="schedule", description="Schedule a match, or launch the interactive fixture wizard")
@app_commands.guild_only()
@app_commands.describe(when="Kickoff in UTC, format: YYYY-MM-DD HH:MM")
@app_commands.autocomplete(team1=team_autocomplete, team2=team_autocomplete)
async def schedule(
    interaction: discord.Interaction, team1: Optional[str] = None, team2: Optional[str] = None, when: Optional[str] = None
) -> None:
    if not team1 or not team2 or not when:
        return await interaction.response.send_message(
            "Step 1 — Select the home team.", view=ScheduleWizard(interaction.user.id), ephemeral=True,
        )
    t1, t2 = bot.store.team(team1), bot.store.team(team2)
    if not t1 or not t2:
        return await interaction.response.send_message("❌ One of those teams does not exist.", ephemeral=True)
    if team1 == team2:
        return await interaction.response.send_message("❌ A team can't play itself.", ephemeral=True)
    if not (is_admin(interaction) or _is_team_staff(interaction, team1) or _is_team_staff(interaction, team2)):
        return await interaction.response.send_message(
            "❌ Only an admin or a manager of one of the teams can schedule this.", ephemeral=True
        )
    try:
        kickoff = datetime.strptime(when.strip(), "%Y-%m-%d %H:%M").replace(tzinfo=timezone.utc)
    except ValueError:
        return await interaction.response.send_message(
            "❌ Bad date. Use `YYYY-MM-DD HH:MM` in UTC, e.g. `2026-07-01 19:30`.", ephemeral=True
        )

    division = t1.get("division", "?")
    match_id = bot.store.next_match_id()
    bot.store.matches[match_id] = {
        "id": match_id,
        "guild_id": interaction.guild.id,
        "division": division,
        "team1": team1,
        "team2": team2,
        "scheduled_for": kickoff.isoformat(),
        "status": "scheduled",
        "score1": None,
        "score2": None,
        "reported_by": None,
        "season": bot.store.season,
        "reminded": False,
        "reminder_stages": [],
        "confirmations": [],
        "fixture_status": "Awaiting Confirmation",
        "fixture_message_id": None,
        "fixture_channel_id": None,
        "match_channel_id": None,
        "goals": {}, "assists": {}, "mvps": [], "clean_sheets": [], "player_stats_applied": False,
        "created": datetime.now(timezone.utc).isoformat(),
    }
    match = bot.store.matches[match_id]
    private_channel = await create_private_match_channel(interaction.guild, match)
    match["match_channel_id"] = private_channel.id if private_channel else None
    announcement_channel = interaction.channel
    if isinstance(announcement_channel, discord.abc.Messageable):
        try:
            message = await announcement_channel.send(embed=fixture_embed(interaction.guild, match), view=FixtureConfirmationView(match_id))
            match["fixture_message_id"] = message.id; match["fixture_channel_id"] = message.channel.id
        except discord.HTTPException:
            log.exception("Could not publish interactive fixture %s", match_id)
    await bot.store.save()

    await interaction.response.send_message(f"✅ Fixture `{match_id}` created. Managers have been asked to confirm.", ephemeral=True)


def round_robin(teams: list[str]) -> list[list[tuple[str, str]]]:
    """Single round-robin schedule (circle method). Returns a list of matchweeks,
    each a list of (home, away) pairs. Odd team counts get a bye each week."""
    ts = list(teams)
    if len(ts) % 2:
        ts.append(None)  # bye marker
    n = len(ts)
    weeks: list[list[tuple[str, str]]] = []
    for _ in range(n - 1):
        pairs = []
        for i in range(n // 2):
            a, b = ts[i], ts[n - 1 - i]
            if a is not None and b is not None:
                pairs.append((a, b))
        weeks.append(pairs)
        ts = [ts[0]] + [ts[-1]] + ts[1:-1]  # rotate, keep first fixed
    return weeks


@bot.tree.command(name="generate-fixtures", description="Auto-generate a full round-robin schedule for a division (Admin only)")
@app_commands.guild_only()
@app_commands.describe(
    start_date="First matchweek date, YYYY-MM-DD (e.g. the opening Saturday)",
    time="Kickoff time UTC, HH:MM (default 19:00)",
    interval_days="Days between matchweeks (default 7)",
    deadline_days="Days after a matchweek opens that it's due (default 5 = Sat→Thu)",
    replace="Delete existing unplayed fixtures for this division first",
)
@app_commands.autocomplete(division=division_autocomplete)
async def generate_fixtures(
    interaction: discord.Interaction,
    division: str,
    start_date: str,
    time: str = "19:00",
    interval_days: int = 7,
    deadline_days: int = 5,
    replace: bool = False,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    div = division
    try:
        start = datetime.strptime(f"{start_date.strip()} {time.strip()}", "%Y-%m-%d %H:%M").replace(tzinfo=timezone.utc)
    except ValueError:
        return await interaction.response.send_message(
            "❌ Bad date/time. Use `start_date` = `YYYY-MM-DD` and `time` = `HH:MM` (UTC).", ephemeral=True
        )

    # Every team stored in this division.
    in_div = [(n, t) for n, t in bot.store.teams.items() if t.get("division") == div]
    if len(bot.guilds) <= 1:
        # Single server: trust the stored division — don't drop a team just
        # because its role/channels were deleted and recreated.
        teams = sorted(n for n, _ in in_div)
        excluded: list[str] = []
    else:
        teams = sorted(n for n, t in in_div if team_in_guild(interaction.guild, n, t))
        excluded = sorted(n for n, t in in_div if n not in teams)

    if len(teams) < 2:
        return await interaction.response.send_message(
            f"❌ Need at least 2 teams in **{div}** (found {len(teams)}). "
            "Check `/list-teams` — teams must be created with `/create-team` and filed in this division.",
            ephemeral=True,
        )

    season = bot.store.season
    existing = [
        mid for mid, m in bot.store.matches.items()
        if m.get("guild_id") == interaction.guild.id
        and m.get("division") == div
        and m.get("season") == season
        and m.get("status") in ("scheduled", "reported", "disputed")
    ]
    if existing and not replace:
        return await interaction.response.send_message(
            f"⚠️ **{div}** already has {len(existing)} scheduled fixture(s) this season. "
            f"Re-run with `replace: True` to regenerate (confirmed results are kept).\n\n"
            f"Teams it will use ({len(teams)}): {', '.join(teams)}",
            ephemeral=True,
        )

    await interaction.response.defer()
    for mid in existing:
        bot.store.matches.pop(mid, None)

    weeks = round_robin(teams)
    created = 0
    for wi, pairs in enumerate(weeks):
        kickoff = start + timedelta(days=interval_days * wi)
        deadline = kickoff + timedelta(days=deadline_days)
        for home, away in pairs:
            mid = bot.store.next_match_id()
            bot.store.matches[mid] = {
                "id": mid,
                "guild_id": interaction.guild.id,
                "division": div,
                "team1": home,
                "team2": away,
                "scheduled_for": kickoff.isoformat(),
                "deadline": deadline.isoformat(),
                "matchweek": wi + 1,
                "status": "scheduled",
                "score1": None,
                "score2": None,
                "reported_by": None,
                "season": season,
                "reminded": False,
                "created": datetime.now(timezone.utc).isoformat(),
            }
            created += 1
    await bot.store.save()

    # The matches are now scheduled and saved; a board-refresh hiccup (e.g. the
    # bot lacking Manage Channels) shouldn't fail the whole command.
    board_note = ""
    try:
        await refresh_division_fixtures(interaction.guild)
    except Exception:  # noqa: BLE001
        log.exception("Fixtures generated but board refresh failed for %s.", div)
        board_note = "\n\n⚠️ Couldn't update the fixtures board — check I have **Manage Channels** & **Manage Messages**, then run `/refresh-records`."

    byes = " (odd team count — one bye per week)" if len(teams) % 2 else ""
    embed = discord.Embed(
        title=f"📅 {div} Fixtures Generated",
        description=f"**{created}** matches across **{len(weeks)}** matchweeks for **{len(teams)}** teams{byes}.{board_note}",
        color=discord.Color.green(),
    )
    embed.add_field(name="Matchweek 1", value=start.strftime("%Y-%m-%d %H:%M UTC"), inline=True)
    embed.add_field(name="Cadence", value=f"every {interval_days} days · due +{deadline_days} days", inline=True)
    embed.add_field(name=f"Teams ({len(teams)})", value=", ".join(teams)[:1024], inline=False)
    if excluded:
        embed.add_field(
            name="⚠️ Left out (role/channels missing in this server)",
            value=", ".join(excluded)[:1024],
            inline=False,
        )
    embed.set_footer(text="See the division's fixtures board · edit individual games with /schedule or /cancel-match")
    await interaction.followup.send(embed=embed)


@bot.tree.command(name="post-fixtures", description="Post a game week's fixtures and PING both teams (Admin only)")
@app_commands.guild_only()
@app_commands.describe(
    week="Game week number to post",
    channel="Where to post (defaults to here)",
    match_format="Series format shown in the header (default from config, e.g. BO5)",
)
@app_commands.autocomplete(division=division_autocomplete)
async def post_fixtures(
    interaction: discord.Interaction,
    division: str,
    week: int,
    channel: Optional[discord.TextChannel] = None,
    match_format: Optional[str] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    div = division
    fixtures = sorted(
        (
            m for m in bot.store.matches.values()
            if m.get("guild_id") == interaction.guild.id
            and m.get("division") == div
            and m.get("season") == bot.store.season
            and m.get("matchweek") == week
            and m.get("status") in ("scheduled", "reported", "disputed")
        ),
        key=lambda m: m.get("scheduled_for") or "",
    )
    if not fixtures:
        return await interaction.response.send_message(
            f"❌ No unplayed fixtures found for **{div}** game week **{week}**. "
            "Generate them first with `/generate-fixtures`.",
            ephemeral=True,
        )

    fmt = (match_format or bot.store.settings.get("match_format", "BO5")).strip()
    deadline = _fmt_date(fixtures[0].get("deadline"))
    divider = "━━━━━━━━━━━━━━━━━━"

    lines = [f"🏆 **GW{week} — {div} Fixtures**", f"**Format:** {fmt}"]
    if deadline:
        lines.append(f"**Deadline:** These fixtures must be played **before the end of {deadline}** ⚠️")
    lines.append(divider)
    lines.append("")
    for m in fixtures:
        lines.append(
            f"{team_mention(interaction.guild, m.get('team1',''))} vs "
            f"{team_mention(interaction.guild, m.get('team2',''))}"
        )
        lines.append("")
    lines.append(divider)
    content = "\n".join(lines)
    if len(content) > 1990:
        content = content[:1985] + "\n…"

    target = channel or interaction.channel
    try:
        await target.send(
            content=content,
            allowed_mentions=discord.AllowedMentions(roles=True, users=False, everyone=False),
        )
    except (discord.Forbidden, discord.HTTPException):
        return await interaction.response.send_message(
            f"❌ Couldn't post in {target.mention} — check my permissions there.", ephemeral=True
        )
    await interaction.response.send_message(
        f"✅ Posted GW{week} {div} fixtures in {target.mention} and pinged {len(fixtures)*2} team role(s).",
        ephemeral=True,
    )


def apply_player_stats(match: dict[str, Any]) -> None:
    """Apply optional `user_id:amount` match stat input once on confirmation."""
    if match.get("player_stats_applied"): return
    for field in ("goals", "assists"):
        for user_id, amount in (match.get(field) or {}).items():
            player = bot.store.players.setdefault(str(user_id), {})
            player.setdefault("goals", 0); player.setdefault("assists", 0); player.setdefault("mvps", 0); player.setdefault("appearances", 0); player.setdefault("clean_sheets", 0)
            player[field] += int(amount)
    for user_id in match.get("mvps", []):
        bot.store.players.setdefault(str(user_id), {}).setdefault("mvps", 0); bot.store.players[str(user_id)]["mvps"] += 1
    for user_id in match.get("clean_sheets", []):
        bot.store.players.setdefault(str(user_id), {}).setdefault("clean_sheets", 0); bot.store.players[str(user_id)]["clean_sheets"] += 1
    for team_name in (match["team1"], match["team2"]):
        for user_id in (bot.store.team(team_name) or {}).get("roster", []):
            player = bot.store.players.setdefault(str(user_id), {}); player["appearances"] = player.get("appearances", 0) + 1
    match["player_stats_applied"] = True


def parse_stat_pairs(raw: str) -> dict[str, int]:
    values: dict[str, int] = {}
    for item in filter(None, (part.strip() for part in raw.split(","))):
        user_id, amount = item.split(":", 1)
        if not user_id.isdigit() or int(amount) < 0: raise ValueError
        values[user_id] = int(amount)
    return values


@bot.tree.command(name="report-result", description="Report a match score (a team manager or admin)")
@app_commands.guild_only()
@app_commands.describe(score1="First team's score", score2="Second team's score")
@app_commands.autocomplete(match=match_autocomplete)
async def report_result(
    interaction: discord.Interaction, match: str, score1: int, score2: int, goals: str = "", assists: str = "", mvp: Optional[discord.Member] = None, clean_sheet: Optional[discord.Member] = None
) -> None:
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if m["status"] == "confirmed":
        return await interaction.response.send_message("❌ That match is already confirmed.", ephemeral=True)
    if score1 < 0 or score2 < 0 or score1 == score2:
        return await interaction.response.send_message(
            "❌ Scores must be non-negative and can't be a tie.", ephemeral=True
        )
    if not (_is_team_staff(interaction, m["team1"]) or _is_team_staff(interaction, m["team2"])):
        return await interaction.response.send_message(
            "❌ Only a manager of one of the teams (or an admin) can report this.", ephemeral=True
        )

    m["score1"], m["score2"] = score1, score2
    try:
        m["goals"], m["assists"] = parse_stat_pairs(goals), parse_stat_pairs(assists)
    except ValueError:
        return await interaction.response.send_message("❌ Goals and assists must use `user_id:amount, user_id:amount`.", ephemeral=True)
    m["mvps"] = [mvp.id] if mvp else []
    m["clean_sheets"] = [clean_sheet.id] if clean_sheet else []
    m["status"] = "reported"
    m["reported_by"] = interaction.user.id
    await bot.store.save()

    # Identify the opponent who must confirm.
    reporter_team = m["team1"] if _is_team_staff(interaction, m["team1"]) else m["team2"]
    opponent = m["team2"] if reporter_team == m["team1"] else m["team1"]
    opp_mgr_id = (bot.store.team(opponent) or {}).get("manager")
    opp_mention = f"<@{opp_mgr_id}>" if opp_mgr_id else f"**{opponent}**"

    embed = discord.Embed(
        title="📊 Result Reported — awaiting confirmation",
        description=f"{team_mention(interaction.guild, m['team1'])} {score1} – {score2} {team_mention(interaction.guild, m['team2'])}",
        color=discord.Color.orange(),
    )
    embed.add_field(
        name="Confirm?",
        value=f"{opp_mention}, run `/confirm-result {match}` to confirm or `/dispute-result {match}` to dispute.",
        inline=False,
    )
    embed.set_footer(text=f"Match {match}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="confirm-result", description="Confirm a reported result (opponent or admin)")
@app_commands.guild_only()
@app_commands.autocomplete(match=match_autocomplete)
async def confirm_result(interaction: discord.Interaction, match: str) -> None:
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if m["status"] != "reported":
        return await interaction.response.send_message("❌ That match has no reported result to confirm.", ephemeral=True)

    # The confirmer must be the team that did NOT report (or an admin).
    reporter_id = m.get("reported_by")
    reporter_is_t1 = reporter_id == (bot.store.team(m["team1"]) or {}).get("manager")
    opponent = m["team2"] if reporter_is_t1 else m["team1"]
    if not (is_admin(interaction) or _is_team_staff(interaction, opponent)):
        return await interaction.response.send_message(
            "❌ Only the opposing team's manager or an admin can confirm.", ephemeral=True
        )

    m["status"] = "confirmed"
    apply_player_stats(m)
    await apply_match_result(interaction.guild, m)
    await refresh_division_records(interaction.guild)
    private_channel = interaction.guild.get_channel(m.get("match_channel_id")) if m.get("match_channel_id") else None
    archive_id = bot.store.settings.get("match_archive_category_id")
    archive = interaction.guild.get_channel(archive_id) if archive_id else None
    if isinstance(private_channel, discord.TextChannel) and isinstance(archive, discord.CategoryChannel):
        try:
            await private_channel.edit(category=archive, reason="ECRL fixture completed")
        except discord.HTTPException:
            log.exception("Could not archive match channel for %s", match)

    embed = discord.Embed(
        title="✅ Result Confirmed",
        description=f"{team_mention(interaction.guild, m['team1'])} {m['score1']} – {m['score2']} {team_mention(interaction.guild, m['team2'])}",
        color=discord.Color.green(),
    )
    embed.set_footer(text=f"Match {match} · standings updated")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="dispute-result", description="Dispute a reported result (opponent or admin)")
@app_commands.guild_only()
@app_commands.autocomplete(match=match_autocomplete)
async def dispute_result(interaction: discord.Interaction, match: str) -> None:
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if m["status"] != "reported":
        return await interaction.response.send_message("❌ Nothing to dispute on that match.", ephemeral=True)
    m["status"] = "disputed"
    await bot.store.save()
    await interaction.response.send_message(
        f"⚠️ Match **{match}** marked **disputed**. An admin can resolve it with "
        f"`/report-result` (re-report) or `/forfeit`.",
    )


@bot.tree.command(name="forfeit", description="Award a forfeit win (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(match=match_autocomplete, winner=team_autocomplete)
async def forfeit(interaction: discord.Interaction, match: str, winner: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if winner not in (m["team1"], m["team2"]):
        return await interaction.response.send_message("❌ That team isn't in this match.", ephemeral=True)
    if m["team1"] == winner:
        m["score1"], m["score2"] = 1, 0
    else:
        m["score1"], m["score2"] = 0, 1
    m["status"] = "confirmed"
    m["forfeit"] = True
    await apply_match_result(interaction.guild, m)
    await refresh_division_records(interaction.guild)
    await interaction.response.send_message(
        f"🏳️ Forfeit recorded — **{winner}** wins match **{match}**. Standings updated."
    )


@bot.tree.command(name="cancel-match", description="Cancel/delete a match (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(match=match_autocomplete)
async def cancel_match(interaction: discord.Interaction, match: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    m = bot.store.matches.pop(match, None)
    if not m or m.get("guild_id") != interaction.guild.id:
        if m:
            bot.store.matches[match] = m  # not ours; put it back
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    await bot.store.save()
    if m["status"] == "confirmed":
        await refresh_division_records(interaction.guild)
    await interaction.response.send_message(f"🗑️ Match **{match}** cancelled.")


@bot.tree.command(name="fixtures", description="Upcoming scheduled matches")
@app_commands.guild_only()
@app_commands.autocomplete(division=division_autocomplete)
async def fixtures(
    interaction: discord.Interaction, division: Optional[str] = None
) -> None:
    div = division if division else None
    upcoming = sorted(
        (
            m for m in bot.store.matches.values()
            if m.get("guild_id") == interaction.guild.id
            and m["status"] in ("scheduled", "reported", "disputed")
            and (div is None or m.get("division") == div)
        ),
        key=lambda m: m.get("scheduled_for") or "",
    )
    if not upcoming:
        return await interaction.response.send_message("No upcoming fixtures.", ephemeral=True)
    lines = []
    for m in upcoming[:25]:
        when = (m.get("scheduled_for") or "")[:16].replace("T", " ")
        tag = {"reported": " ⏳ awaiting confirm", "disputed": " ⚠️ disputed"}.get(m["status"], "")
        lines.append(f"`{m['id']}` **{m['team1']}** vs **{m['team2']}** — {when} UTC{tag}")
    embed = discord.Embed(
        title=f"📅 Fixtures{f' — {div}' if div else ''}",
        description="\n".join(lines),
        color=discord.Color.blue(),
    )
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="results", description="Recent confirmed results")
@app_commands.guild_only()
@app_commands.autocomplete(division=division_autocomplete)
async def results(
    interaction: discord.Interaction, division: Optional[str] = None
) -> None:
    div = division if division else None
    done = sorted(
        (
            m for m in bot.store.matches.values()
            if m.get("guild_id") == interaction.guild.id
            and m["status"] == "confirmed"
            and (div is None or m.get("division") == div)
        ),
        key=lambda m: m.get("scheduled_for") or m.get("created") or "",
        reverse=True,
    )
    if not done:
        return await interaction.response.send_message("No results yet.", ephemeral=True)
    lines = []
    for m in done[:25]:
        ff = " 🏳️" if m.get("forfeit") else ""
        lines.append(f"`{m['id']}` **{m['team1']} {m['score1']}–{m['score2']} {m['team2']}**{ff}")
    embed = discord.Embed(
        title=f"📊 Results{f' — {div}' if div else ''}",
        description="\n".join(lines),
        color=discord.Color.green(),
    )
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="match-history", description="A team's match results")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def match_history(interaction: discord.Interaction, team: str) -> None:
    if not bot.store.team(team):
        return await interaction.response.send_message(f"❌ Team **{team}** does not exist.", ephemeral=True)
    matches = sorted(
        (
            m for m in bot.store.matches.values()
            if m.get("guild_id") == interaction.guild.id
            and m["status"] == "confirmed"
            and team in (m["team1"], m["team2"])
        ),
        key=lambda m: m.get("scheduled_for") or m.get("created") or "",
        reverse=True,
    )
    if not matches:
        return await interaction.response.send_message(f"No results yet for **{team}**.", ephemeral=True)
    w = l = 0
    lines = []
    for m in matches[:25]:
        us, them = (m["score1"], m["score2"]) if m["team1"] == team else (m["score2"], m["score1"])
        opp = m["team2"] if m["team1"] == team else m["team1"]
        if us > them:
            w += 1; mark = "🟢 W"
        else:
            l += 1; mark = "🔴 L"
        lines.append(f"{mark} {us}–{them} vs **{opp}**")
    embed = discord.Embed(
        title=f"📜 {team} — Match History",
        description="\n".join(lines),
        color=discord.Color.blurple(),
    )
    embed.set_footer(text=f"Record: {w}W – {l}L")
    await interaction.response.send_message(embed=embed)


# --------------------------------------------------------------------------- #
# Season & configuration
# --------------------------------------------------------------------------- #

@bot.tree.command(name="season-start", description="Start a new season — resets standings (Admin only)")
@app_commands.guild_only()
async def season_start(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    bot.store.settings["current_season"] = bot.store.season + 1
    await bot.store.save()
    await refresh_division_records(interaction.guild)
    await interaction.response.send_message(
        f"🏁 **Season {bot.store.season}** has begun! Standings are reset; "
        "previous results are kept in history."
    )


@bot.tree.command(name="season-info", description="Show the current season")
@app_commands.guild_only()
async def season_info(interaction: discord.Interaction) -> None:
    season = bot.store.season
    played = sum(
        1 for m in bot.store.matches.values()
        if m.get("guild_id") == interaction.guild.id
        and m.get("season") == season and m["status"] == "confirmed"
    )
    embed = discord.Embed(
        title=f"📆 {bot.store.settings.get('league_name', 'The Titan Elite Division')} — Season {season}",
        color=discord.Color.blurple(),
    )
    embed.add_field(name="Matches played", value=str(played), inline=True)
    embed.add_field(name="Transfer window", value="Open" if bot.store.window_open else "Closed", inline=True)
    embed.add_field(name="Rosters", value="Locked" if bot.store.rosters_locked else "Open", inline=True)
    await interaction.response.send_message(embed=embed)


class ConfirmResetView(discord.ui.View):
    def __init__(self, author_id: int, remove_team_roles: bool) -> None:
        super().__init__(timeout=60)
        self.author_id = author_id
        self.remove_team_roles = remove_team_roles

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("This isn't your confirmation.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Yes, wipe all data", style=discord.ButtonStyle.danger)
    async def wipe(self, interaction: discord.Interaction, _: discord.ui.Button) -> None:
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild

        # Delete each team's Discord role (e.g. "Furia Iberia (EL)"). Channels are NOT touched.
        roles_removed = 0
        if self.remove_team_roles:
            targets: list[discord.Role] = []
            for name, team in bot.store.teams.items():
                rid = team.get("role_id")
                role = guild.get_role(rid) if rid else None
                if role is None:  # fallback for legacy teams stored before role_id
                    role = discord.utils.get(guild.roles, name=team_role_name(name, team.get("division", "")))
                if role is not None:
                    targets.append(role)
            for role in targets:
                try:
                    await role.delete(reason="ECRL league reset")
                    roles_removed += 1
                except discord.HTTPException:
                    log.warning("Could not delete role %s (is it above the bot's role?).", role.name)

        # Wipe stored data.
        bot.store.teams.clear()
        bot.store.players.clear()
        bot.store.matches.clear()
        bot.store.settings["match_counter"] = 0
        bot.store.settings["current_season"] = 1
        await bot.store.save()
        for refresh in (refresh_division_records, refresh_division_fixtures):
            try:
                await refresh(guild)
            except Exception:
                log.exception("Board refresh failed after reset.")

        role_note = f" and removed **{roles_removed}** team role(s)" if self.remove_team_roles else ""
        await interaction.followup.send(
            f"🧹 **League data wiped.** All teams, rosters, matches and fixtures cleared, season reset to **1**"
            f"{role_note}. Channels were left untouched. Ready for a fresh start.",
            ephemeral=True,
        )
        self.stop()

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, _: discord.ui.Button) -> None:
        await interaction.response.edit_message(content="Cancelled — nothing was deleted.", view=None)
        self.stop()


@bot.tree.command(name="reset-league", description="Wipe ALL league data — teams, rosters, matches (Admin only)")
@app_commands.guild_only()
@app_commands.describe(
    confirm="Type CONFIRM (all caps) to proceed",
    remove_team_roles="Also delete each team's Discord role, e.g. 'Furia Iberia (EL)' (default: yes)",
)
async def reset_league(
    interaction: discord.Interaction, confirm: str, remove_team_roles: bool = True
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if confirm != "CONFIRM":
        return await interaction.response.send_message(
            "⚠️ This permanently wipes **all** teams, rosters, matches and fixtures.\n"
            "To proceed, run it again with `confirm: CONFIRM`.",
            ephemeral=True,
        )
    team_count = len(bot.store.teams)
    match_count = len(bot.store.matches)
    role_line = (
        "Team roles (e.g. `Furia Iberia (EL)`) **will be deleted**. Channels are kept."
        if remove_team_roles
        else "Roles and channels are **kept**."
    )
    await interaction.response.send_message(
        f"⚠️ **Final check.** This will delete **{team_count}** team(s) and **{match_count}** match(es) "
        f"and reset to Season 1.\n{role_line}\nThis cannot be undone.",
        view=ConfirmResetView(interaction.user.id, remove_team_roles),
        ephemeral=True,
    )


def _collect_team_roles(guild: discord.Guild) -> list[discord.Role]:
    """Every team role in the server — the 'Name (DIV)' roles — excluding the
    Team Manager / Co-Manager roles. Uses stored role IDs plus a name-pattern scan."""
    found: dict[int, discord.Role] = {}
    # stored team role IDs (precise)
    for team in bot.store.teams.values():
        rid = team.get("role_id")
        role = guild.get_role(rid) if rid else None
        if role:
            found[role.id] = role
    # name-pattern scan (catches orphaned/renamed roles too)
    for role in guild.roles:
        low = role.name.lower()
        if "manager" in low:  # never touch Team Manager / Co-Manager roles
            continue
        if any(role.name.endswith(f"({div})") for div in DIVISIONS):
            found[role.id] = role
    return list(found.values())


class ConfirmRemoveRolesView(discord.ui.View):
    def __init__(self, author_id: int) -> None:
        super().__init__(timeout=60)
        self.author_id = author_id

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("This isn't your confirmation.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Delete all team roles", style=discord.ButtonStyle.danger)
    async def wipe(self, interaction: discord.Interaction, _: discord.ui.Button) -> None:
        await interaction.response.defer(ephemeral=True)
        removed = 0
        for role in _collect_team_roles(interaction.guild):
            try:
                await role.delete(reason="Remove all team roles")
                removed += 1
            except discord.HTTPException:
                log.warning("Could not delete role %s (above the bot's role?).", role.name)
        await interaction.followup.send(
            f"🧹 Removed **{removed}** team role(s). Team data and channels were left untouched.",
            ephemeral=True,
        )
        self.stop()

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def cancel(self, interaction: discord.Interaction, _: discord.ui.Button) -> None:
        await interaction.response.edit_message(content="Cancelled — nothing was deleted.", view=None)
        self.stop()


@bot.tree.command(name="remove-team-roles", description="Delete ALL team roles, e.g. 'Furia Iberia (EL)' (Admin only)")
@app_commands.guild_only()
async def remove_team_roles(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    targets = _collect_team_roles(interaction.guild)
    if not targets:
        return await interaction.response.send_message("No team roles found to remove.", ephemeral=True)
    preview = ", ".join(r.name for r in targets[:15]) + ("…" if len(targets) > 15 else "")
    await interaction.response.send_message(
        f"⚠️ This will delete **{len(targets)}** team role(s):\n{preview}\n\n"
        "Team Manager / Co-Manager roles, team data and channels are **kept**. This cannot be undone.",
        view=ConfirmRemoveRolesView(interaction.user.id),
        ephemeral=True,
    )


@bot.tree.command(name="export-server", description="Export all roles and channels to a downloadable file (Admin only)")
@app_commands.guild_only()
async def export_server(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    gid = interaction.guild_id

    # Pull roles and channels straight from Discord's REST API as raw data. This
    # needs neither the guild cache nor fetch_guild, so it works on a server the
    # bot was just added to.
    try:
        raw_roles = await bot.http.get_roles(gid)
        raw_channels = await bot.http.get_all_guild_channels(gid)
    except discord.HTTPException as exc:
        return await interaction.followup.send(
            f"❌ Discord wouldn't return this server's data (HTTP {getattr(exc, 'status', '?')}). "
            "Make sure the bot has the **View Channels** permission here, then try again.",
            ephemeral=True)

    guild = interaction.guild or bot.get_guild(gid)
    gname = guild.name if guild else "server"

    CH_TYPES = {0: "text", 2: "voice", 4: "category", 5: "announcement",
                13: "stage", 15: "forum", 16: "media"}

    def ctype(n: Any) -> str:
        return CH_TYPES.get(n, f"type_{n}")

    # Roles (highest first, skipping @everyone whose id == guild id).
    roles = []
    for r in sorted(raw_roles, key=lambda r: r.get("position", 0), reverse=True):
        if int(r["id"]) == gid:
            continue
        roles.append({
            "id": r["id"],
            "name": r.get("name"),
            "color": f"#{int(r.get('color', 0)):06X}",
            "position": r.get("position"),
            "hoist": r.get("hoist", False),
            "mentionable": r.get("mentionable", False),
            "managed": r.get("managed", False),
            "permissions": str(r.get("permissions", "0")),
        })

    def chan_entry(c: dict) -> dict:
        entry = {"id": c["id"], "name": c.get("name"), "type": ctype(c.get("type")), "position": c.get("position")}
        if c.get("topic"):
            entry["topic"] = c["topic"]
        return entry

    cats = {c["id"]: c for c in raw_channels if c.get("type") == 4}
    grouped: dict[str, list] = {cid: [] for cid in cats}
    uncategorized = []
    for c in sorted(raw_channels, key=lambda c: c.get("position", 0)):
        if c.get("type") == 4:
            continue
        parent = c.get("parent_id")
        if parent in grouped:
            grouped[parent].append(chan_entry(c))
        else:
            uncategorized.append(chan_entry(c))

    channels: dict[str, Any] = {"uncategorized": uncategorized, "categories": []}
    for cid, cat in sorted(cats.items(), key=lambda kv: kv[1].get("position", 0)):
        channels["categories"].append({
            "id": cid, "name": cat.get("name"), "position": cat.get("position"),
            "channels": grouped.get(cid, []),
        })

    total_channels = sum(1 for c in raw_channels if c.get("type") != 4)
    export = {
        "guild": {"id": gid, "name": gname},
        "exported_at": datetime.now(timezone.utc).isoformat(),
        "counts": {"roles": len(roles), "categories": len(channels["categories"]), "channels": total_channels},
        "roles": roles,
        "channels": channels,
    }

    data = json.dumps(export, indent=2, ensure_ascii=False).encode("utf-8")
    fname = f"{(gname or 'server').replace(' ', '_')}_export_{datetime.now(timezone.utc):%Y%m%d}.json"
    file = discord.File(io.BytesIO(data), filename=fname)
    await interaction.followup.send(
        f"📦 Exported **{export['counts']['roles']}** roles and "
        f"**{export['counts']['channels']}** channels across "
        f"**{export['counts']['categories']}** categories.",
        file=file, ephemeral=True,
    )


@bot.tree.command(name="auto-configure", description="Detect this server's league channels & manager roles (Admin only)")
@app_commands.guild_only()
async def auto_configure(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild or bot.get_guild(interaction.guild_id)
    if guild is None:
        return await interaction.followup.send("❌ Couldn't read this server yet — restart the bot and try again.", ephemeral=True)

    leagues = bot.store.settings.setdefault("leagues", {})
    embed = discord.Embed(title="⚙️ Auto-configure — detected mapping", color=discord.Color.blurple())
    for div in DIVISIONS:
        token = LEAGUE_TOKENS[div]
        cfg = leagues.setdefault(div, {})
        info_cat = find_info_category(guild, div)
        roster = (next((c for c in guild.text_channels if token in _norm(c.name).split() and "roster" in _norm(c.name)), None)
                  or (next((c for c in info_cat.text_channels if "roster" in _norm(c.name)), None) if info_cat else None))
        fa = next((c for c in guild.text_channels if token in _norm(c.name).split() and "free agent" in _norm(c.name)), None)
        fixtures = detect_fixtures_channel(guild, div)
        mgr = next((r for r in guild.roles if token in _norm(r.name).split() and "manager" in _norm(r.name) and "co manager" not in _norm(r.name)), None)
        co = next((r for r in guild.roles if token in _norm(r.name).split() and "co manager" in _norm(r.name)), None)
        team_cat = find_team_category(guild, div)
        if roster:
            cfg["rosters_channel"] = roster.id
        if fa:
            cfg["fa_channel"] = fa.id
        if fixtures:
            cfg["fixtures_channel"] = fixtures.id
        if mgr:
            cfg["manager_role"] = mgr.id
        if co:
            cfg["co_manager_role"] = co.id
        if team_cat:
            cfg["team_category"] = team_cat.id
        embed.add_field(
            name=f"{div} League",
            value=(f"Rosters: {roster.mention if roster else '—'}\n"
                   f"Fixtures: {fixtures.mention if fixtures else '—'}\n"
                   f"Free agents: {fa.mention if fa else '—'}\n"
                   f"Manager: {mgr.mention if mgr else '—'}\n"
                   f"Co-Manager: {co.mention if co else '—'}\n"
                   f"Team category: {team_cat.name if team_cat else '—'}"),
            inline=True,
        )
    await bot.store.save()
    embed.set_footer(text="Anything showing — can be set manually with /set-league.")
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="setup-rosters", description="Create a rosters channel for each league (or one) and post boards (Admin only)")
@app_commands.guild_only()
@app_commands.describe(league="Just one league (leave blank for all)")
@app_commands.autocomplete(league=division_autocomplete)
async def setup_rosters(interaction: discord.Interaction, league: Optional[str] = None) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild or bot.get_guild(interaction.guild_id)
    if guild is None:
        return await interaction.followup.send("❌ Couldn't read this server yet — restart the bot and try again.", ephemeral=True)

    targets = [league] if league else DIVISIONS
    results = []
    for d in targets:
        ch = await ensure_league_rosters_channel(guild, d)
        results.append((d, ch))
    await bot.store.save()
    try:
        await refresh_division_records(guild)
    except Exception:
        log.exception("Board refresh failed after setup-rosters.")

    embed = discord.Embed(title="📜 Roster channels", color=discord.Color.blurple())
    for d, ch in results:
        embed.add_field(name=f"{d} League", value=(ch.mention if ch else "⚠️ no league category found"), inline=True)
    embed.set_footer(text="Roster boards posted/refreshed. They update automatically from here.")
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="set-league", description="Manually set a league's channels & manager roles (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(league=division_autocomplete)
@app_commands.describe(
    rosters_channel="Channel where this league's roster board posts",
    fa_channel="Channel for this league's free-agent announcements",
    fixtures_channel="Channel where this league's fixtures post",
    manager_role="Role to ping as this league's manager",
    co_manager_role="Role to ping as this league's co-manager",
    team_category="Category where new team channels are created",
    eligible_role="Role granted to verified players in this league's rank band",
)
async def set_league(
    interaction: discord.Interaction,
    league: str,
    rosters_channel: Optional[discord.TextChannel] = None,
    fa_channel: Optional[discord.TextChannel] = None,
    fixtures_channel: Optional[discord.TextChannel] = None,
    manager_role: Optional[discord.Role] = None,
    co_manager_role: Optional[discord.Role] = None,
    team_category: Optional[discord.CategoryChannel] = None,
    eligible_role: Optional[discord.Role] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if league not in DIVISIONS:
        return await interaction.response.send_message("❌ Choose a configured league.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    cfg = league_cfg(league)
    if rosters_channel:
        cfg["rosters_channel"] = rosters_channel.id
    if fa_channel:
        cfg["fa_channel"] = fa_channel.id
    if fixtures_channel:
        cfg["fixtures_channel"] = fixtures_channel.id
    if manager_role:
        cfg["manager_role"] = manager_role.id
        try:
            if not manager_role.mentionable:
                await manager_role.edit(mentionable=True, reason="Enable Team Manager free-agent pings")
        except discord.HTTPException:
            return await interaction.followup.send("❌ I couldn't enable mentions for this manager role.", ephemeral=True)
    else:
        try:
            cfg["manager_role"] = (await league_manager_role(interaction.guild, league)).id
        except discord.HTTPException:
            return await interaction.followup.send("❌ I couldn't create or configure this league's manager role.", ephemeral=True)
    if co_manager_role:
        cfg["co_manager_role"] = co_manager_role.id
    elif not interaction.guild.get_role(cfg.get("co_manager_role")):
        try:
            cfg["co_manager_role"] = (await league_co_manager_role(interaction.guild, league)).id
        except discord.HTTPException:
            return await interaction.followup.send("❌ I couldn't create this league's co-manager role.", ephemeral=True)
    if team_category:
        cfg["team_category"] = team_category.id
    elif not interaction.guild.get_channel(cfg.get("team_category")):
        try:
            cfg["team_category"] = (await get_or_create_category(interaction.guild, f"{league} Teams")).id
        except discord.HTTPException:
            return await interaction.followup.send("❌ I couldn't create this league's team category.", ephemeral=True)
    if eligible_role:
        cfg["eligible_role"] = eligible_role.id
    elif _find_eligible_role(interaction.guild, league) is None:
        try:
            role = await get_or_create_role(
                interaction.guild,
                f"{league_display_name(league)} Eligible",
                color=discord.Color.teal(),
            )
            cfg["eligible_role"] = role.id
        except discord.HTTPException:
            return await interaction.followup.send(
                "❌ I couldn't create this league's eligible role. Give the bot Manage Roles and move its role above the role list, then retry.",
                ephemeral=True,
            )
    await bot.store.save()
    await interaction.followup.send(
        f"✅ Updated **{league_display_name(league)}** mapping.", ephemeral=True)


def rank_band_conflict(ranks: list[str], excluding: Optional[str] = None) -> Optional[tuple[str, str]]:
    for code in DIVISIONS:
        if code == excluding:
            continue
        existing = set(league_cfg(code).get("ranks", []))
        overlap = next((rank for rank in ranks if rank in existing), None)
        if overlap:
            return code, overlap
    return None


@bot.tree.command(name="league-list", description="Show configured leagues and rank bands (Admin only)")
@app_commands.guild_only()
async def league_list(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    lines = []
    for code in DIVISIONS:
        cfg = league_cfg(code)
        band = mmr_band_label(cfg) if cfg.get("min_mmr") is not None else cfg.get("rank_band", "rank band not set")
        name = cfg.get("display_name") or f"{code} League"
        details = f"{cfg['mode']} · {band}" if cfg.get("mode") else str(band)
        rows = cfg.get("rosters_channel")
        fixtures = cfg.get("fixtures_channel")
        lines.append(f"**{name} ({code})** — {details} · rosters: {f'<#{rows}>' if rows else 'unset'} · fixtures: {f'<#{fixtures}>' if fixtures else 'unset'}")
    await interaction.response.send_message("\n".join(lines) or "No leagues configured.", ephemeral=True)


def mmr_band_conflict(
    mode: str, lower: int, upper: Optional[int], excluding: Optional[str] = None,
) -> Optional[tuple[str, int]]:
    """Return the first configured same-playlist MMR range that overlaps."""
    for code in DIVISIONS:
        if code == excluding:
            continue
        cfg = league_cfg(code)
        if cfg.get("mode") != mode or cfg.get("min_mmr") is None:
            continue
        old_lower = int(cfg["min_mmr"])
        old_upper = cfg.get("max_mmr")
        if (upper is None or old_lower <= upper) and (old_upper is None or lower <= int(old_upper)):
            return code, max(lower, old_lower)
    return None


@bot.tree.command(name="league-create-mmr", description="Create a queue-specific MMR league (Admin only)")
@app_commands.guild_only()
@app_commands.choices(mode=[app_commands.Choice(name=p, value=p) for p in ("3v3", "2v2")])
@app_commands.describe(
    code="Short unique code, such as SL3 or TL2",
    display_name="Public league name, such as SSL League",
    mode="Competitive playlist",
    min_mmr="Lowest MMR in this league",
    max_mmr="Highest MMR, leave blank for no upper limit",
)
async def league_create_mmr(
    interaction: discord.Interaction,
    code: str,
    display_name: str,
    mode: app_commands.Choice[str],
    min_mmr: app_commands.Range[int, 0, 5000],
    max_mmr: Optional[app_commands.Range[int, 0, 5000]] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    code = code.strip().upper()
    display_name = display_name.strip()
    if not re.fullmatch(r"[A-Z0-9]{1,6}", code):
        return await interaction.response.send_message("❌ Use a short code with 1–6 letters or numbers.", ephemeral=True)
    if not display_name or len(display_name) > 80:
        return await interaction.response.send_message("❌ Enter a league name from 1 to 80 characters.", ephemeral=True)
    if code in DIVISIONS or code in bot.store.settings.get("leagues", {}):
        return await interaction.response.send_message(f"❌ **{code}** is already in use.", ephemeral=True)
    if max_mmr is not None and max_mmr < min_mmr:
        return await interaction.response.send_message("❌ The maximum MMR must be at least the minimum MMR.", ephemeral=True)
    if len(DIVISIONS) >= 25:
        return await interaction.response.send_message("❌ Discord supports at most 25 leagues in these command suggestions.", ephemeral=True)
    conflict = mmr_band_conflict(mode.value, min_mmr, max_mmr)
    if conflict:
        return await interaction.response.send_message(
            f"❌ {conflict[1]} MMR already belongs to **{league_display_name(conflict[0])}** in {mode.value}.",
            ephemeral=True,
        )
    guild = interaction.guild
    if guild is None:
        return await interaction.response.send_message("❌ Use this command in the server.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    cfg = league_cfg(code)
    band = f"{min_mmr}+" if max_mmr is None else f"{min_mmr}-{max_mmr}"
    cfg.update({
        "display_name": display_name,
        "mode": mode.value,
        "team_size": int(mode.value[0]),
        "min_mmr": int(min_mmr),
        "max_mmr": int(max_mmr) if max_mmr is not None else None,
        "rank_band": band,
        "ranks": [],
    })
    try:
        cfg["manager_role"] = (await league_manager_role(guild, code)).id
        cfg["co_manager_role"] = (await league_co_manager_role(guild, code)).id
        cfg["team_category"] = (await get_or_create_category(guild, f"{code} Teams")).id
        cfg["eligible_role"] = (await get_or_create_role(
            guild, f"{display_name} Eligible", color=discord.Color.teal()
        )).id
    except discord.Forbidden:
        bot.store.settings["leagues"].pop(code, None)
        return await interaction.followup.send(
            "❌ I need Manage Roles and Manage Channels to create this league's roles/category.", ephemeral=True)
    except discord.HTTPException as exc:
        bot.store.settings["leagues"].pop(code, None)
        return await interaction.followup.send(f"❌ Discord could not create the league resources ({exc}).", ephemeral=True)
    bot.store.settings.setdefault("division_codes", []).append(code)
    refresh_division_state()
    await bot.store.save()
    await interaction.followup.send(
        f"✅ Created **{display_name} ({code})** for **{mode.value} · {mmr_band_label(cfg)}**. "
        "Use `/set-league` to connect existing roster, fixtures, and free-agent channels.",
        ephemeral=True,
    )


@bot.tree.command(name="league-set-mmr", description="Change a league's playlist and MMR range (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(league=division_autocomplete)
@app_commands.choices(mode=[app_commands.Choice(name=p, value=p) for p in ("3v3", "2v2")])
@app_commands.describe(
    league="League to update",
    mode="Competitive playlist",
    min_mmr="Lowest MMR in this league",
    max_mmr="Highest MMR, leave blank for no upper limit",
)
async def league_set_mmr(
    interaction: discord.Interaction,
    league: str,
    mode: app_commands.Choice[str],
    min_mmr: app_commands.Range[int, 0, 5000],
    max_mmr: Optional[app_commands.Range[int, 0, 5000]] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if league not in DIVISIONS:
        return await interaction.response.send_message("❌ Choose a configured league.", ephemeral=True)
    if max_mmr is not None and max_mmr < min_mmr:
        return await interaction.response.send_message("❌ The maximum MMR must be at least the minimum MMR.", ephemeral=True)
    conflict = mmr_band_conflict(mode.value, min_mmr, max_mmr, excluding=league)
    if conflict:
        return await interaction.response.send_message(
            f"❌ {conflict[1]} MMR already belongs to **{league_display_name(conflict[0])}** in {mode.value}.",
            ephemeral=True,
        )
    cfg = league_cfg(league)
    cfg.update({
        "mode": mode.value,
        "team_size": int(mode.value[0]),
        "min_mmr": int(min_mmr),
        "max_mmr": int(max_mmr) if max_mmr is not None else None,
        "rank_band": f"{min_mmr}+" if max_mmr is None else f"{min_mmr}-{max_mmr}",
        "ranks": [],
    })
    await bot.store.save()
    await interaction.response.send_message(
        f"✅ **{league_display_name(league)}** now covers **{mode.value} · {mmr_band_label(cfg)}**.",
        ephemeral=True,
    )


@bot.tree.command(name="league-create", description="Create a league, its roles, category, and rank band (Admin only)")
@app_commands.guild_only()
@app_commands.describe(
    code="Short league code, such as SL or EL",
    rank_band="Examples: SSL+, GC2-3, C3-GC1, C1-2, D1-3",
    rosters_channel="Existing roster board channel (optional)",
    fixtures_channel="Existing fixtures channel (optional)",
    fa_channel="League free-agent channel (optional; uses the global channel if blank)",
    manager_role="Existing manager role (optional)",
    co_manager_role="Existing co-manager role (optional)",
    team_category="Existing team category (optional)",
    eligible_role="Existing rank-eligibility role (optional)",
)
async def league_create(
    interaction: discord.Interaction,
    code: str,
    rank_band: str,
    rosters_channel: Optional[discord.TextChannel] = None,
    fixtures_channel: Optional[discord.TextChannel] = None,
    fa_channel: Optional[discord.TextChannel] = None,
    manager_role: Optional[discord.Role] = None,
    co_manager_role: Optional[discord.Role] = None,
    team_category: Optional[discord.CategoryChannel] = None,
    eligible_role: Optional[discord.Role] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    code = code.strip().upper()
    if not re.fullmatch(r"[A-Z0-9]{1,6}", code):
        return await interaction.response.send_message("❌ Use a short code with 1–6 letters or numbers.", ephemeral=True)
    if code in DIVISIONS:
        return await interaction.response.send_message(f"❌ **{code}** already exists. Use `/league-set-ranks` to change its rank band.", ephemeral=True)
    if code in bot.store.settings.get("leagues", {}):
        return await interaction.response.send_message(f"❌ **{code}** is already reserved in the saved league settings.", ephemeral=True)
    if len(DIVISIONS) >= 25:
        return await interaction.response.send_message("❌ Discord supports at most 25 leagues in these command suggestions.", ephemeral=True)
    try:
        ranks = expand_rank_band(rank_band)
    except ValueError as exc:
        return await interaction.response.send_message(f"❌ {exc}", ephemeral=True)
    conflict = rank_band_conflict(ranks)
    if conflict:
        return await interaction.response.send_message(
            f"❌ **{conflict[1]}** is already assigned to **{conflict[0]}**. Change that band's range first.",
            ephemeral=True)
    guild = interaction.guild
    if guild is None:
        return await interaction.response.send_message("❌ Use this command in the server.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)

    cfg = league_cfg(code)
    cfg.update({"rank_band": rank_band.strip(), "ranks": ranks})
    try:
        cfg["manager_role"] = (manager_role or await league_manager_role(guild, code)).id
        cfg["co_manager_role"] = (co_manager_role or await league_co_manager_role(guild, code)).id
        category = team_category or await get_or_create_category(guild, f"{code} Teams")
        cfg["team_category"] = category.id
        if eligible_role is None:
            eligible_role = _find_eligible_role(guild, code)
        if eligible_role is None:
            eligible_role = await get_or_create_role(guild, f"{code} Eligible", color=discord.Color.teal())
        cfg["eligible_role"] = eligible_role.id
    except discord.Forbidden:
        bot.store.settings["leagues"].pop(code, None)
        return await interaction.followup.send(
            "❌ I need Manage Roles and Manage Channels to create this league's default roles/category. "
            "You can also rerun the command with existing roles and category selected.", ephemeral=True)
    except discord.HTTPException as exc:
        bot.store.settings["leagues"].pop(code, None)
        return await interaction.followup.send(f"❌ Discord could not create the league resources ({exc}).", ephemeral=True)

    for key, value in (("rosters_channel", rosters_channel), ("fixtures_channel", fixtures_channel), ("fa_channel", fa_channel)):
        if value:
            cfg[key] = value.id
    bot.store.settings.setdefault("division_codes", []).append(code)
    refresh_division_state()
    await bot.store.save()
    await interaction.followup.send(
        f"✅ Created **{code}** for **{rank_band.strip()}**. I set up its manager roles, eligibility role, and team category. "
        "Use `/set-league` to connect roster and fixtures channels if you did not select them here.", ephemeral=True)


@bot.tree.command(name="league-set-ranks", description="Change a league's rank band (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(league=division_autocomplete)
@app_commands.describe(rank_band="Examples: SSL+, GC2-3, C3-GC1, C1-2, D1-3")
async def league_set_ranks(interaction: discord.Interaction, league: str, rank_band: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    if league not in DIVISIONS:
        return await interaction.response.send_message("❌ Choose a configured league.", ephemeral=True)
    try:
        ranks = expand_rank_band(rank_band)
    except ValueError as exc:
        return await interaction.response.send_message(f"❌ {exc}", ephemeral=True)
    conflict = rank_band_conflict(ranks, excluding=league)
    if conflict:
        return await interaction.response.send_message(
            f"❌ **{conflict[1]}** is already assigned to **{conflict[0]}**.", ephemeral=True)
    cfg = league_cfg(league)
    cfg["rank_band"] = rank_band.strip()
    cfg["ranks"] = ranks
    for key in ("mode", "min_mmr", "max_mmr"):
        cfg.pop(key, None)
    await bot.store.save()
    await interaction.response.send_message(f"✅ **{league}** now covers **{rank_band.strip()}**.", ephemeral=True)


@bot.tree.command(name="league-rename", description="Rename a league code and migrate its saved data (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(old_code=division_autocomplete)
@app_commands.describe(
    old_code="League to rename",
    new_code="New short code",
    new_name="Optional new public league name, for example a sponsor name",
)
async def league_rename(
    interaction: discord.Interaction,
    old_code: str,
    new_code: str,
    new_name: Optional[str] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    new_code = new_code.strip().upper()
    if old_code not in DIVISIONS:
        return await interaction.response.send_message("❌ Choose a configured league.", ephemeral=True)
    if not re.fullmatch(r"[A-Z0-9]{1,6}", new_code):
        return await interaction.response.send_message("❌ Use a short code with 1–6 letters or numbers.", ephemeral=True)
    if new_code in DIVISIONS:
        return await interaction.response.send_message(f"❌ **{new_code}** already exists.", ephemeral=True)

    settings = bot.store.settings
    leagues = settings.setdefault("leagues", {})
    if new_code in leagues:
        return await interaction.response.send_message(f"❌ **{new_code}** is already reserved in the saved league settings.", ephemeral=True)
    cfg = leagues.pop(old_code, {})
    if new_name and new_name.strip():
        cfg["display_name"] = new_name.strip()[:80]
    elif cfg.get("display_name") and cfg["display_name"].lower().startswith(old_code.lower()):
        cfg["display_name"] = cfg["display_name"].replace(old_code, new_code, 1)
    leagues[new_code] = cfg
    codes = settings.setdefault("division_codes", DIVISIONS.copy())
    settings["division_codes"] = [new_code if code == old_code else code for code in codes]
    for team in bot.store.teams.values():
        if team.get("division") == old_code:
            team["division"] = new_code
    for match in bot.store.matches.values():
        if match.get("division") == old_code:
            match["division"] = new_code
    for player in bot.store.players.values():
        for key in ("last_division", "eligible_division"):
            if player.get(key) == old_code:
                player[key] = new_code
    for section in ("records", "fixtures_msgs"):
        for per_guild in settings.get(section, {}).values():
            if old_code in per_guild:
                per_guild[new_code] = per_guild.pop(old_code)
    refresh_division_state()
    await bot.store.save()
    await interaction.response.send_message(
        f"✅ Renamed **{old_code}** to **{new_code}** in league settings, teams, players, and fixtures. "
        + (f"The public name is now **{cfg['display_name']}**. " if cfg.get("display_name") else "")
        + "The saved Discord role/category IDs stay connected; rename their visible labels in Discord if needed.",
        ephemeral=True)


@bot.tree.command(name="server-data", description="Overview of all teams and data the bot tracks (Admin only)")
@app_commands.guild_only()
async def server_data(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild or bot.get_guild(interaction.guild_id)
    settings = bot.store.settings

    def who(uid: Optional[int]) -> str:
        m = guild.get_member(uid) if (guild and uid) else None
        return m.display_name if m else (f"user {uid}" if uid else "—")

    teams = [(n, t) for n, t in bot.store.teams.items()
             if guild is None or team_in_guild(guild, n, t)]
    by_div: dict[str, list] = {d: [] for d in DIVISIONS}
    other: list = []
    for n, t in teams:
        (by_div[t.get("division")] if t.get("division") in by_div else other).append((n, t))

    total_players = 0
    formats = ", ".join(sorted({format_label(code) for code in DIVISIONS})) or format_label()
    lines = [f"# {settings.get('league_name', 'League')} — Server Data",
             f"Season {settings.get('current_season', 1)}  |  "
             f"Window {'OPEN' if bot.store.window_open else 'closed'}  |  "
             f"Roster cap {settings.get('roster_max', 0)}  |  Formats {formats}", ""]
    for d in DIVISIONS + (["(no league)"] if other else []):
        group = other if d == "(no league)" else by_div[d]
        lines.append(f"## {d} — {len(group)} team(s)")
        for name, t in sorted(group):
            roster = t.get("roster", [])
            total_players += len(roster)
            staff = t.get("staff", {}) or {}
            co = ", ".join(who(u) for ids in staff.values() for u in ids) if staff else ""
            played = "played" if t.get("has_played_match") else "no matches yet"
            lines.append(f"- **{name}** — Manager: {who(t.get('manager'))} · "
                         f"{len(roster)} player(s)" + (f" · Co/Staff: {co}" if co else "") + f" · {played}")
        lines.append("")

    fa = collect_free_agents(guild) if guild else []
    gid = interaction.guild_id
    matches = sum(1 for mt in bot.store.matches.values() if mt.get("guild_id") == gid)
    lines.append(f"**Totals:** {len(teams)} teams · {total_players} rostered players · "
                 f"{len(fa)} free agents · {matches} matches recorded")

    report = "\n".join(lines)

    summary = discord.Embed(title=f"📊 {settings.get('league_name', 'League')} — Server Data",
                            color=discord.Color.blurple())
    summary.add_field(name="Teams", value=str(len(teams)), inline=True)
    summary.add_field(name="Rostered players", value=str(total_players), inline=True)
    summary.add_field(name="Free agents", value=str(len(fa)), inline=True)
    summary.add_field(name="Per league",
                      value=" · ".join(f"{d}: {len(by_div[d])}" for d in DIVISIONS) or "—", inline=False)
    summary.add_field(name="Season / Window",
                      value=f"S{settings.get('current_season', 1)} · "
                            f"{'OPEN' if bot.store.window_open else 'closed'}", inline=True)

    if len(report) <= 1800:
        await interaction.followup.send(f"{report}", embed=summary, ephemeral=True)
    else:
        file = discord.File(io.BytesIO(report.encode("utf-8")), filename="server-data.md")
        summary.set_footer(text="Full breakdown attached.")
        await interaction.followup.send(embed=summary, file=file, ephemeral=True)


_NONTEAM_KEYWORDS = ("manager", "co manager", "eligible", "coach", "owner", "staff", "admin",
                     "free agent", "rfa", "team manager", "organiser", "organizer", "verified",
                     "booster", "content creator", "platinum", "diamond", "silver", "bronze",
                     "ssl", "grand champion", "sapphire", "founder", "partnership", "welcomer")


def _looks_nonteam(role: discord.Role) -> bool:
    if role.is_default() or role.managed:
        return True
    low = _norm(role.name)
    if not low or set(role.name) <= set("=—-_ "):  # divider roles
        return True
    return any(k in low for k in _NONTEAM_KEYWORDS)


def _name_and_div(role: discord.Role) -> Optional[tuple[str, Optional[str]]]:
    """Return (clean_team_name, division_or_None) for a plausible team role, or None
    if the role clearly isn't a team. Division may be None (resolved later by channel)."""
    if _looks_nonteam(role):
        return None
    name = role.name
    low = _norm(name)
    tag_map = {code.lower(): code for code in DIVISIONS}
    tag_map.update({"a": "A", "x": "X", "b": "B", "academy": "Academy", "aca": "Academy"})

    # 1) "(X)" suffix
    m = re.search(r"\(([^)]+)\)\s*$", name)
    if m and m.group(1).strip().lower() in tag_map:
        team = name[: m.start()].strip()
        return (team or name, tag_map[m.group(1).strip().lower()])

    # 2) "… X team" / "… academy team"
    tag_pattern = "|".join(re.escape(tag) for tag in sorted(tag_map, key=len, reverse=True))
    m2 = re.search(rf"\b({tag_pattern})\s+team\b", low)
    if m2:
        team = re.sub(r"\b(a|x|b|academy)\s+team\b", "", name, flags=re.IGNORECASE).strip(" -")
        return (team or name, tag_map[m2.group(1)])

    # 3) bare trailing single letter, e.g. "Nivai B", "Zenith x", "ghostline strikers a"
    m3 = re.search(r"\s([axb])$", name, flags=re.IGNORECASE)
    if m3:
        return (name[: m3.start()].strip() or name, tag_map[m3.group(1).lower()])

    # 4) trailing "academy" (keep full name; it's usually part of the team name)
    if low.endswith("academy"):
        return (name, "Academy")

    # 5) plausible team role, league unknown — resolve from its channel later.
    return (name, None)


def _team_division_by_channel(guild: discord.Guild) -> dict[int, str]:
    """Map role_id -> league by looking at which league team-channel category a role
    has access to (e.g. 'A league Team channels', 'X league team chats')."""
    out: dict[int, str] = {}
    for cat in guild.categories:
        cn = _norm(cat.name)
        if not any(w in cn for w in ("team", "chat", "channel")):
            continue
        div = next((d for d, tok in LEAGUE_TOKENS.items() if tok in cn.split()), None)
        if not div:
            continue
        for ch in cat.channels:
            for target, ow in ch.overwrites.items():
                if isinstance(target, discord.Role) and not _looks_nonteam(target):
                    if ow.view_channel is not False:  # role can see this team channel
                        out.setdefault(target.id, div)
    return out


@bot.tree.command(name="import-teams", description="Scan the server for existing team roles and save them (Admin only)")
@app_commands.guild_only()
async def import_teams(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild or bot.get_guild(interaction.guild_id)
    if guild is None:
        return await interaction.followup.send("❌ Couldn't read this server yet — restart the bot and try again.", ephemeral=True)

    existing_role_ids = {t.get("role_id") for t in bot.store.teams.values() if t.get("role_id")}
    existing_names = {n.lower() for n in bot.store.teams}
    by_channel = _team_division_by_channel(guild)  # role_id -> division fallback

    imported: list[tuple[str, str, int]] = []
    needs_league: list[str] = []
    skipped = 0
    for role in guild.roles:
        res = _name_and_div(role)
        if not res:
            continue
        _, division = res
        team_name = role.name.strip()  # keep the FULL role name so 'Vision (X)' and 'Vision (B)' stay distinct
        if division is None:
            division = by_channel.get(role.id)
        # No league from name or channel: still import it (unassigned) if it's a
        # plausible team role (mentionable), so no team is lost — assign later.
        if division is None and not role.mentionable:
            continue
        if role.id in existing_role_ids or team_name.lower() in existing_names:
            skipped += 1
            continue
        existing_names.add(team_name.lower())

        members = [m.id for m in role.members]
        manager = None
        for m in role.members:
            if any("manager" in r.name.lower() and "co" not in r.name.lower() for r in m.roles):
                manager = m.id
                break
        if manager is None and members:
            manager = members[0]

        bot.store.teams[team_name] = {
            "manager": manager, "division": division, "roster": members,
            "staff": {}, "has_played_match": False, "role_id": role.id,
            "text_channel_id": None, "voice_channel_id": None,
            "created": datetime.now(timezone.utc).isoformat(), "imported": True,
        }
        if division:
            imported.append((team_name, division, len(members)))
        else:
            needs_league.append(team_name)

    await bot.store.save()
    try:
        await refresh_division_records(guild)
    except Exception:
        log.exception("Board refresh failed after import.")

    total = len(imported) + len(needs_league)
    if total == 0:
        return await interaction.followup.send(
            f"No new team roles detected (skipped {skipped} already-tracked).", ephemeral=True)

    by_div: dict[str, list] = {}
    for tn, dv, cnt in imported:
        by_div.setdefault(dv, []).append(f"{tn} ({cnt})")
    embed = discord.Embed(
        title=f"📥 Imported {total} team(s)",
        description="Rosters filled from role members. Review with `/server-data`; "
                    "fix a wrong manager with `/set-manager`.",
        color=discord.Color.green())
    for dv in DIVISIONS:
        if dv in by_div:
            embed.add_field(name=f"{dv} League ({len(by_div[dv])})",
                            value="\n".join(sorted(by_div[dv]))[:1024], inline=False)
    if needs_league:
        embed.add_field(
            name=f"❔ Imported but no league detected ({len(needs_league)})",
            value=("Set each with `/set-team-league`:\n" + ", ".join(sorted(needs_league)))[:1024],
            inline=False)
    embed.set_footer(text=f"{skipped} already-tracked skipped.")
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="set-team-league", description="Assign or change a team's league (Admin only)")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
@app_commands.autocomplete(league=division_autocomplete)
async def set_team_league(interaction: discord.Interaction, team: str, league: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    team_data = bot.store.team(team)
    if not team_data:
        return await interaction.response.send_message(f"❌ Team **{team}** does not exist.", ephemeral=True)
    team_data["division"] = league
    await bot.store.save()
    try:
        await refresh_division_records(interaction.guild)
    except Exception:
        log.exception("Board refresh failed after set-team-league.")
    await interaction.response.send_message(f"✅ **{team}** is now in **{league}** League.", ephemeral=True)


CONFIG_KEYS = {
    "league_name": ("text", "League name shown on standings"),
    "audit_channel": ("text", "Name of the audit-log channel (blank to disable)"),
    "signing_approval_channel": ("text", "Channel where signings await staff confirmation (blank = audit channel)"),
    "points_win": ("int", "Points awarded for a win"),
    "points_loss": ("int", "Points awarded for a loss"),
    "roster_max": ("int", "Max players per team (0 = unlimited)"),
    "roster_min": ("int", "Minimum players per team (informational)"),
    "team_size": ("int", "Players per side (2 = 2v2, 3 = 3v3)"),
    "rosters_locked": ("bool", "Block signings/joins (true/false)"),
    "free_agent_channel": ("text", "Channel name for free-agent announcements"),
    "free_agent_interval_hours": ("int", "How often to post free agents (hours)"),
    "free_agent_ping": ("bool", "Ping manager roles in announcements (true/false)"),
    "free_agent_stagger_seconds": ("int", "Delay between each free-agent post (seconds)"),
    "match_channel_category_id": ("int", "Category ID for private match channels (0 disables creation)"),
    "match_archive_category_id": ("int", "Category ID for completed-match archive (0 disables archiving)"),
}


@bot.tree.command(name="config", description="Change a league setting (Admin only)")
@app_commands.guild_only()
@app_commands.describe(setting="Which setting to change", value="New value")
@app_commands.choices(setting=[app_commands.Choice(name=k, value=k) for k in CONFIG_KEYS])
async def config(interaction: discord.Interaction, setting: app_commands.Choice[str], value: str) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    kind, _desc = CONFIG_KEYS[setting.value]
    parsed: Any = value
    if kind == "int":
        try:
            parsed = int(value)
        except ValueError:
            return await interaction.response.send_message("❌ That setting needs a whole number.", ephemeral=True)
    elif kind == "bool":
        if value.lower() not in ("true", "false", "yes", "no", "on", "off"):
            return await interaction.response.send_message("❌ Use `true` or `false`.", ephemeral=True)
        parsed = value.lower() in ("true", "yes", "on")
    bot.store.settings[setting.value] = parsed
    await bot.store.save()
    if setting.value == "free_agent_interval_hours":
        free_agent_loop.change_interval(hours=max(1, int(parsed)))
    await interaction.response.send_message(f"✅ `{setting.value}` set to **{parsed}**.", ephemeral=True)


@bot.tree.command(name="config-view", description="Show current league settings (Admin only)")
@app_commands.guild_only()
async def config_view(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    s = bot.store.settings
    lines = [f"**{k}**: `{s.get(k)}`" for k in CONFIG_KEYS]
    lines.append(f"**current_season**: `{s.get('current_season')}`")
    lines.append(f"**transfer_window_open**: `{s.get('transfer_window_open')}`")
    embed = discord.Embed(title="⚙️ League Settings", description="\n".join(lines), color=discord.Color.greyple())
    await interaction.response.send_message(embed=embed, ephemeral=True)


# --------------------------------------------------------------------------- #
# Utility commands
# --------------------------------------------------------------------------- #

@bot.tree.command(name="ping", description="Check bot status")
async def ping(interaction: discord.Interaction) -> None:
    latency_ms = round(bot.latency * 1000)
    _ln = bot.store.settings.get("league_name", "The Titan Elite Division")
    await interaction.response.send_message(f"✅ {_ln} bot is online — {latency_ms} ms.")


@bot.tree.command(name="version", description="Show the bot version and quick stats")
@app_commands.guild_only()
async def version_cmd(interaction: discord.Interaction) -> None:
    teams = sum(1 for n, t in bot.store.teams.items() if team_in_guild(interaction.guild, n, t))
    matches = sum(1 for m in bot.store.matches.values() if m.get("guild_id") == interaction.guild.id)
    embed = discord.Embed(
        title=f"🤖 {bot.store.settings.get('league_name', 'The Titan Elite Division')}",
        color=discord.Color.blurple(),
    )
    embed.add_field(name="Version", value=BOT_VERSION, inline=True)
    embed.add_field(name="Commands", value=str(len(bot.tree.get_commands())), inline=True)
    embed.add_field(name="Season", value=str(bot.store.season), inline=True)
    embed.add_field(name="Teams here", value=str(teams), inline=True)
    embed.add_field(name="Matches here", value=str(matches), inline=True)
    embed.add_field(name="Latency", value=f"{round(bot.latency * 1000)} ms", inline=True)
    await interaction.response.send_message(embed=embed, ephemeral=True)


def _team_matches(guild: discord.Guild, team_name: str, *, status: Optional[str] = None) -> list[dict[str, Any]]:
    """All of a team's matches in this guild (optionally filtered by status)."""
    out = []
    for m in bot.store.matches.values():
        if m.get("guild_id") != guild.id:
            continue
        if team_name not in (m.get("team1"), m.get("team2")):
            continue
        if status and m.get("status") != status:
            continue
        out.append(m)
    return out


@bot.tree.command(name="next-match", description="Show your team's (or a given team's) next scheduled match")
@app_commands.guild_only()
@app_commands.describe(team="Team to look up (defaults to your own team)")
@app_commands.autocomplete(team=team_autocomplete)
async def next_match(interaction: discord.Interaction, team: Optional[str] = None) -> None:
    team = team or bot.store.find_member_team(interaction.user.id)
    if not team or not bot.store.team(team):
        return await interaction.response.send_message(
            "❌ You're not on a team — pass a `team` to look one up.", ephemeral=True
        )
    upcoming = sorted(
        (m for m in _team_matches(interaction.guild, team) if m.get("status") in ("scheduled", "reported", "disputed")),
        key=lambda m: m.get("scheduled_for") or "",
    )
    if not upcoming:
        return await interaction.response.send_message(f"📭 **{team}** has no upcoming matches.", ephemeral=True)
    m = upcoming[0]
    opp = m["team2"] if m["team1"] == team else m["team1"]
    when = (m.get("scheduled_for") or "").replace("T", " ")[:16]
    ddl = (m.get("deadline") or "")[:10]
    embed = discord.Embed(title=f"⏭️ Next match — {team}", color=discord.Color.blue())
    embed.add_field(name="Opponent", value=opp, inline=True)
    if m.get("matchweek"):
        embed.add_field(name="Matchweek", value=str(m["matchweek"]), inline=True)
    embed.add_field(name="Kickoff (UTC)", value=when or "TBD", inline=True)
    if ddl:
        embed.add_field(name="Deadline", value=ddl, inline=True)
    embed.set_footer(text=f"Match {m['id']} · {m['status']}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="head-to-head", description="Compare two teams' confirmed head-to-head record")
@app_commands.guild_only()
@app_commands.autocomplete(team1=team_autocomplete, team2=team_autocomplete)
async def head_to_head(interaction: discord.Interaction, team1: str, team2: str) -> None:
    if team1 == team2:
        return await interaction.response.send_message("❌ Pick two different teams.", ephemeral=True)
    games = [
        m for m in bot.store.matches.values()
        if m.get("guild_id") == interaction.guild.id
        and m.get("status") == "confirmed"
        and {m.get("team1"), m.get("team2")} == {team1, team2}
    ]
    if not games:
        return await interaction.response.send_message(
            f"📭 No confirmed matches between **{team1}** and **{team2}** yet.", ephemeral=True
        )
    w1 = w2 = 0
    lines = []
    for m in sorted(games, key=lambda x: x.get("scheduled_for") or ""):
        s1, s2 = m.get("score1", 0), m.get("score2", 0)
        # normalise so team1's score is first regardless of home/away
        a, b = (s1, s2) if m["team1"] == team1 else (s2, s1)
        if a > b:
            w1 += 1
        elif b > a:
            w2 += 1
        lines.append(f"`{(m.get('scheduled_for') or '')[:10] or m['id']}` {team1} {a}–{b} {team2}")
    embed = discord.Embed(
        title=f"⚔️ {team1} vs {team2}",
        description=f"**{w1} – {w2}** across {len(games)} confirmed match(es)",
        color=discord.Color.gold(),
    )
    embed.add_field(name="History", value="\n".join(lines)[:1024], inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="team-form", description="A team's recent results and current standing")
@app_commands.guild_only()
@app_commands.autocomplete(team=team_autocomplete)
async def team_form(interaction: discord.Interaction, team: str) -> None:
    t = bot.store.team(team)
    if not t:
        return await interaction.response.send_message("❌ Unknown team.", ephemeral=True)
    division = t.get("division")
    confirmed = sorted(
        (m for m in _team_matches(interaction.guild, team, status="confirmed")),
        key=lambda m: m.get("scheduled_for") or m.get("created") or "",
    )
    recent = confirmed[-5:]
    form = []
    detail = []
    for m in recent:
        a, b = (m.get("score1", 0), m.get("score2", 0)) if m["team1"] == team else (m.get("score2", 0), m.get("score1", 0))
        opp = m["team2"] if m["team1"] == team else m["team1"]
        form.append("🟩W" if a > b else ("🟥L" if b > a else "⬜D"))
        detail.append(f"{'W' if a>b else 'L'} {a}–{b} vs {opp}")
    embed = discord.Embed(title=f"📈 Form — {team}", color=discord.Color.teal())
    embed.add_field(name="Last 5", value=" ".join(form) if form else "No results yet", inline=False)
    if detail:
        embed.add_field(name="Detail", value="\n".join(reversed(detail))[:1024], inline=False)
    # Standing position within its division
    if division:
        rows = compute_standings(interaction.guild, division)
        for i, r in enumerate(rows, 1):
            if r["team"] == team:
                gd = r["GF"] - r["GA"]
                embed.add_field(
                    name=f"{division} standing",
                    value=f"#{i} of {len(rows)} · {r['W']}W-{r['L']}L · {r['Pts']} pts · GD {gd:+d}",
                    inline=False,
                )
                break
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="reschedule", description="Change a match's kickoff time (team manager or admin)")
@app_commands.guild_only()
@app_commands.describe(when="New kickoff in UTC, format: YYYY-MM-DD HH:MM")
@app_commands.autocomplete(match=match_autocomplete)
async def reschedule(interaction: discord.Interaction, match: str, when: str) -> None:
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if m["status"] == "confirmed":
        return await interaction.response.send_message("❌ That match is already played.", ephemeral=True)
    if not (_is_team_staff(interaction, m["team1"]) or _is_team_staff(interaction, m["team2"])):
        return await interaction.response.send_message(
            "❌ Only a manager of one of the teams (or an admin) can reschedule.", ephemeral=True
        )
    try:
        kickoff = datetime.strptime(when.strip(), "%Y-%m-%d %H:%M").replace(tzinfo=timezone.utc)
    except ValueError:
        return await interaction.response.send_message(
            "❌ Bad date. Use `YYYY-MM-DD HH:MM` in UTC, e.g. `2026-07-05 19:30`.", ephemeral=True
        )
    m["scheduled_for"] = kickoff.isoformat()
    m["reminded"] = False  # let the reminder fire again for the new time
    await bot.store.save()
    await refresh_division_fixtures(interaction.guild)
    embed = discord.Embed(
        title="🔄 Match Rescheduled",
        description=f"{team_mention(interaction.guild, m['team1'])} vs {team_mention(interaction.guild, m['team2'])}",
        color=discord.Color.blue(),
    )
    embed.add_field(name="New kickoff (UTC)", value=when.strip(), inline=True)
    embed.set_footer(text=f"Match {match}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="edit-result", description="Correct or set a match score and update standings (Admin only)")
@app_commands.guild_only()
@app_commands.describe(score1="First team's score", score2="Second team's score")
@app_commands.autocomplete(match=match_autocomplete)
async def edit_result(interaction: discord.Interaction, match: str, score1: int, score2: int) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    m = bot.store.matches.get(match)
    if not m or m.get("guild_id") != interaction.guild.id:
        return await interaction.response.send_message("❌ Unknown match.", ephemeral=True)
    if score1 < 0 or score2 < 0 or score1 == score2:
        return await interaction.response.send_message(
            "❌ Scores must be non-negative and can't be a tie.", ephemeral=True
        )
    m["score1"], m["score2"] = score1, score2
    m["status"] = "confirmed"
    await apply_match_result(interaction.guild, m)
    await refresh_division_records(interaction.guild)
    await refresh_division_fixtures(interaction.guild)
    embed = discord.Embed(
        title="✏️ Result Updated",
        description=f"{team_mention(interaction.guild, m['team1'])} {score1} – {score2} {team_mention(interaction.guild, m['team2'])}",
        color=discord.Color.green(),
    )
    embed.set_footer(text=f"Match {match} · standings recomputed")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="clear-fixtures", description="Delete a division's UNPLAYED fixtures this season (Admin only)")
@app_commands.guild_only()
@app_commands.describe(confirm="Set to True to actually delete")
@app_commands.autocomplete(division=division_autocomplete)
async def clear_fixtures(
    interaction: discord.Interaction, division: str, confirm: bool = False
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    div = division
    season = bot.store.season
    victims = [
        mid for mid, m in bot.store.matches.items()
        if m.get("guild_id") == interaction.guild.id
        and m.get("division") == div
        and m.get("season") == season
        and m.get("status") in ("scheduled", "reported", "disputed")
    ]
    if not victims:
        return await interaction.response.send_message(
            f"📭 No unplayed fixtures to clear in **{div}**.", ephemeral=True
        )
    if not confirm:
        return await interaction.response.send_message(
            f"⚠️ This will delete **{len(victims)}** unplayed **{div}** fixture(s) (confirmed results are kept). "
            "Re-run with `confirm: True` to proceed.",
            ephemeral=True,
        )
    for mid in victims:
        bot.store.matches.pop(mid, None)
    await bot.store.save()
    await refresh_division_fixtures(interaction.guild)
    await interaction.response.send_message(
        f"🗑️ Cleared **{len(victims)}** unplayed **{div}** fixture(s).", ephemeral=True
    )


@bot.tree.command(name="overdue", description="List scheduled matches past their deadline (Admin only)")
@app_commands.guild_only()
async def overdue(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    now = datetime.now(timezone.utc)
    late = []
    for m in bot.store.matches.values():
        if m.get("guild_id") != interaction.guild.id:
            continue
        if m.get("status") not in ("scheduled", "reported", "disputed"):
            continue
        ddl = m.get("deadline")
        if not ddl:
            continue
        try:
            if datetime.fromisoformat(ddl) < now:
                late.append(m)
        except ValueError:
            continue
    if not late:
        return await interaction.response.send_message("✅ Nothing overdue — everyone's on schedule.", ephemeral=True)
    late.sort(key=lambda m: m.get("deadline") or "")
    lines = [
        f"`{m['id']}` **{m.get('division','?')}** · {m['team1']} vs {m['team2']} — was due {(m.get('deadline') or '')[:10]}"
        + (" ⏳ reported" if m["status"] == "reported" else (" ⚠️ disputed" if m["status"] == "disputed" else ""))
        for m in late[:25]
    ]
    embed = discord.Embed(
        title="⏰ Overdue Matches",
        description="\n".join(lines)[:4000],
        color=discord.Color.red(),
    )
    embed.set_footer(text=f"{len(late)} overdue · resolve with /report-result, /forfeit or /reschedule")
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="announce", description="Post an embed announcement to a channel (Admin only)")
@app_commands.guild_only()
@app_commands.describe(message="What to announce", channel="Where to post (defaults to here)", title="Optional heading")
async def announce(
    interaction: discord.Interaction,
    message: str,
    channel: Optional[discord.TextChannel] = None,
    title: Optional[str] = None,
) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    target = channel or interaction.channel
    embed = discord.Embed(
        title=title or "📢 Announcement",
        description=message.replace("\\n", "\n"),
        color=discord.Color.blurple(),
        timestamp=datetime.now(timezone.utc),
    )
    embed.set_footer(text=f"— {interaction.user.display_name}")
    try:
        await target.send(embed=embed)
    except (discord.Forbidden, discord.HTTPException):
        return await interaction.response.send_message(
            f"❌ Couldn't post in {target.mention} — check my permissions there.", ephemeral=True
        )
    await interaction.response.send_message(f"✅ Announcement posted in {target.mention}.", ephemeral=True)


@bot.tree.command(name="sync", description="Fix duplicate commands & refresh (Admin only)")
@app_commands.guild_only()
async def force_sync(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    guild_obj = discord.Object(id=interaction.guild_id)
    # Remove any guild-scoped copies (these caused each command to show twice
    # alongside the global ones), then keep a single global command set.
    bot.tree.clear_commands(guild=guild_obj)
    await bot.tree.sync(guild=guild_obj)   # pushes the empty guild set → clears duplicates
    synced = await bot.tree.sync()         # ensure the global set is current
    await interaction.followup.send(
        f"✅ Cleared duplicate commands and synced {len(synced)} global commands. "
        "If you still see doubles, give it a minute and restart Discord.",
        ephemeral=True,
    )


@bot.tree.command(name="refresh-records", description="Rebuild the division roster records now (Admin only)")
@app_commands.guild_only()
async def refresh_records(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    await refresh_division_records(interaction.guild)
    await refresh_division_fixtures(interaction.guild)
    await interaction.followup.send(
        f"✅ Roster & fixtures boards updated. They refresh automatically every {RECORDS_INTERVAL_HOURS} hours.",
        ephemeral=True,
    )


@bot.tree.command(name="announce-free-agents", description="Post free-agent announcements now (Admin only)")
@app_commands.guild_only()
async def announce_free_agents_cmd(interaction: discord.Interaction) -> None:
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    posted = await post_free_agents(interaction.guild)
    interval = bot.store.settings.get("free_agent_interval_hours", 12)
    await interaction.followup.send(
        f"✅ Posted {posted} free-agent announcement(s). They also post automatically every {interval} hours.",
        ephemeral=True,
    )


@bot.tree.command(name="help", description="List bot commands")
async def help_command(interaction: discord.Interaction) -> None:
    league = bot.store.settings.get("league_name", "The Titan Elite Division")
    embed = discord.Embed(title=f"{league} Bot — Commands", color=discord.Color.blurple())
    embed.add_field(
        name="🎮 Players",
        value="`/verify` `/join` `/leave` `/myteam` `/profile` `/link-epic` `/set-rank` `/freeagents`",
        inline=False,
    )
    embed.add_field(
        name="📋 Info",
        value=(
            "`/list-teams` `/team-info` `/team_view_roster` `/team_staff` "
            "`/standings` `/fixtures` `/results` `/match-history` `/season-info` "
            "`/next-match` `/head-to-head` `/team-form`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🏆 Matches (managers)",
        value="`/schedule` `/reschedule` `/report-result` `/confirm-result` `/dispute-result`",
        inline=False,
    )
    embed.add_field(
        name="👔 Managers",
        value="`/sign` (DM offer; eligible players only) `/release_player`",
        inline=False,
    )
    embed.add_field(
        name="🛠️ Admin — teams",
        value=(
            "`/create-team` `/delete-team` `/rename-team` `/set-manager` `/transfer` "
            "`/promote` `/relegate` `/team_add_player` `/team_kick_player` "
            "`/add_staff` `/remove_staff` `/set-team-played`"
        ),
        inline=False,
    )
    embed.add_field(
        name="⚙️ Admin — league",
        value=(
            "`/forfeit` `/cancel-match` `/edit-result` `/generate-fixtures` `/post-fixtures` `/clear-fixtures` "
            "`/overdue` `/announce` `/season-start` `/config` `/config-view` "
            "`/loan` `/close-transfer-window` `/open-transfer-window` "
            "`/announce-free-agents` `/refresh-records` `/sync`"
            " `/league-list` `/league-create` `/league-set-ranks` `/league-create-mmr` `/league-set-mmr` `/league-rename` `/set-league`"
        ),
        inline=False,
    )
    embed.add_field(name="🔧 Utility", value="`/ping` `/version` `/help`", inline=False)
    await interaction.response.send_message(embed=embed, ephemeral=True)


class LeagueDashboardView(ui.View):
    def __init__(self) -> None: super().__init__(timeout=None)
    @ui.button(label="Fixtures", style=discord.ButtonStyle.primary, custom_id="ecrl-dashboard:fixtures")
    async def fixtures_button(self, interaction: discord.Interaction, _: ui.Button) -> None:
        upcoming = [m for m in bot.store.matches.values() if m.get("guild_id") == interaction.guild_id and m.get("status") == "scheduled"]
        text = "\n".join(f"• **{m['team1']} vs {m['team2']}** — {(m.get('scheduled_for') or 'TBC')[:16]} UTC" for m in sorted(upcoming, key=lambda x: x.get("scheduled_for") or "")[:15]) or "No upcoming fixtures."
        await interaction.response.send_message(embed=discord.Embed(title=f"{bot.store.settings.get('league_name', 'The Titan Elites Division')} | Fixtures", description=text, color=discord.Color.blue()), ephemeral=True)
    @ui.button(label="Standings", style=discord.ButtonStyle.primary, custom_id="ecrl-dashboard:standings")
    async def standings_button(self, interaction: discord.Interaction, _: ui.Button) -> None:
        divisions = sorted({t.get("division") for t in bot.store.teams.values() if t.get("division")})
        text = "\n".join(f"**{division}**\n{format_standings_table(compute_standings(interaction.guild, division))}" for division in divisions[:3]) or "No standings available."
        await interaction.response.send_message(embed=discord.Embed(title=f"{bot.store.settings.get('league_name', 'The Titan Elites Division')} | Standings", description=text[:4000], color=discord.Color.gold()), ephemeral=True)
    @ui.button(label="Top Scorers", style=discord.ButtonStyle.primary, custom_id="ecrl-dashboard:scorers")
    async def scorers_button(self, interaction: discord.Interaction, _: ui.Button) -> None:
        await send_stats_embed(interaction)


async def send_stats_embed(interaction: discord.Interaction) -> None:
    players = list(bot.store.players.items())
    def board(key: str) -> str:
        ranked = sorted(players, key=lambda item: item[1].get(key, 0), reverse=True)[:10]
        return "\n".join(f"{index}. <@{user_id}> — **{record.get(key, 0)}**" for index, (user_id, record) in enumerate(ranked, 1)) or "No data yet."
    embed = discord.Embed(title=f"{bot.store.settings.get('league_name', 'The Titan Elites Division')} | Player Statistics", color=discord.Color.purple())
    embed.add_field(name="Golden Boot", value=board("goals"), inline=True)
    embed.add_field(name="Top Assists", value=board("assists"), inline=True)
    embed.add_field(name="MVP Rankings", value=board("mvps"), inline=True)
    embed.add_field(name="Clean Sheets", value=board("clean_sheets"), inline=False)
    if interaction.response.is_done(): await interaction.followup.send(embed=embed, ephemeral=True)
    else: await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="stats", description="Show player leaderboards")
@app_commands.guild_only()
async def stats(interaction: discord.Interaction) -> None:
    await send_stats_embed(interaction)


@bot.tree.command(name="dashboard", description="Show the league dashboard")
@app_commands.guild_only()
async def dashboard(interaction: discord.Interaction) -> None:
    teams = [team for team in bot.store.teams.values() if team_in_guild(interaction.guild, "", team)]
    season = bot.store.season; completed = sum(m.get("status") == "confirmed" and m.get("guild_id") == interaction.guild_id for m in bot.store.matches.values())
    embed = discord.Embed(title=f"{bot.store.settings.get('league_name', 'The Titan Elites Division')} | League Dashboard", color=discord.Color.teal())
    embed.add_field(name="Current Season", value=f"S{season}", inline=True); embed.add_field(name="Transfer Window", value="OPEN" if bot.store.window_open else "CLOSED", inline=True)
    embed.add_field(name="Registered Teams", value=str(len(teams)), inline=True); embed.add_field(name="Registered Players", value=str(len(bot.store.players)), inline=True); embed.add_field(name="Completed Matches", value=str(completed), inline=True)
    await interaction.response.send_message(embed=embed, view=LeagueDashboardView())


# --------------------------------------------------------------------------- #
# Entry point

# --------------------------------------------------------------------------- #
# Verification + smurf/alt risk check
# --------------------------------------------------------------------------- #

VERIFY_RANKS = {r: r for r in (
    "Gold 3", "Platinum 1", "Platinum 2", "Platinum 3",
    "Diamond 1", "Diamond 2", "Diamond 3",
    "Champion 1", "Champion 2", "Champion 3",
    "Grand Champion 1", "Grand Champion 2", "Grand Champion 3",
    "Supersonic Legend 1900", "Supersonic Legend 2000+",
)}
HIGH_RANKS = {"Grand Champion 1", "Grand Champion 2", "Grand Champion 3",
              "Supersonic Legend 1900", "Supersonic Legend 2000+"}
NEW_ACCOUNT_DAYS = 30
HIGH_RANK_NEW_DAYS = 90

def _find_role_ci(guild, name):
    return discord.utils.find(lambda r: r.name.lower() == name.lower(), guild.roles)


def smurf_report(interaction, rl_account, tracker_link, rank, member=None, *, mmr=None):
    flags = []
    member = member or interaction.user
    uid = str(member.id)
    norm = rl_account.strip().lower()
    tracker_norm = tracker_profile_key(tracker_link)
    for other_id, pdata in bot.store.players.items():
        if other_id == uid:
            continue
        if norm and str(pdata.get("epic", "")).strip().lower() == norm:
            flags.append(f"RL username already linked to <@{other_id}>")
        saved_tracker = str(pdata.get("tracker_link", "")).strip()
        if saved_tracker and tracker_profile_key(saved_tracker) == tracker_norm:
            flags.append(f"Tracker profile already submitted by <@{other_id}>")
        if flags:
            break
    age_days = (datetime.now(timezone.utc) - member.created_at).days
    if age_days < NEW_ACCOUNT_DAYS:
        flags.append(f"Discord account only {age_days} day(s) old")
    if (rank in HIGH_RANKS or (mmr is not None and int(mmr) >= 1900)) and age_days < HIGH_RANK_NEW_DAYS:
        flags.append(f"High rank ({rank}) on a {age_days}-day-old account")
    return flags


def _find_eligible_role(guild, league):
    """Find the league's eligible role, e.g. 'A league eligible' / 'Academy eligible'."""
    cfg = league_cfg(league)
    configured = guild.get_role(cfg.get("eligible_role")) if cfg.get("eligible_role") else None
    if configured:
        return configured
    tokens = [LEAGUE_TOKENS.get(league) or _norm(league).replace(" ", "")]
    # The server's original top-league role was named "L2 Eligible". Keep
    # recognizing that same role ID/name while its league code is now SL.
    if league == "SL":
        tokens.append("l2")
    tokens = [token for token in tokens if token]
    if not tokens:
        return None
    for r in guild.roles:
        n = _norm(r.name)
        if any(token in n.split() for token in tokens) and "eligible" in n:
            cfg["eligible_role"] = r.id
            return r
    return None


def league_eligibility_error(member: discord.Member, team: dict[str, Any]) -> Optional[str]:
    """Return why a player cannot join a team in a league they aren't approved for."""
    league = team.get("division")
    if league not in DIVISIONS:
        return "This team is not assigned to an active league. Ask an admin to fix its league first."
    pdata = bot.store.players.get(str(member.id), {})
    status = pdata.get("verification_status")
    if status and status != "approved":
        if status == "pending":
            return f"{member.mention}'s verification is still waiting for staff approval."
        return f"{member.mention} needs an approved `/verify` request before joining a league team."
    role = _find_eligible_role(member.guild, league)
    if role is None:
        return f"The **{league}** eligibility role is not configured. Ask an admin to check `/set-league`."
    if role not in member.roles:
        return f"{member.mention} needs the **{role.name}** role to join a **{league}** team. Use `/verify` first."
    return None


async def _clear_verification_roles(guild, member) -> None:
    """Remove old verification and league eligibility roles after a rejection."""
    names = {
        "verified", "tracker verified", "a league eligible", "x league eligible",
        *VERIFY_RANKS.keys(),
    }
    roles = [r for r in guild.roles if r.name.lower() in {name.lower() for name in names}]
    roles.extend(
        role for code in DIVISIONS
        if (role := _find_eligible_role(guild, code)) is not None
    )
    stale = list({role.id: role for role in roles if role in member.roles}.values())
    if stale:
        try:
            await member.remove_roles(*stale, reason="Verification was not approved")
        except discord.HTTPException:
            log.warning("Could not remove stale verification roles from %s.", member)


async def _apply_verification(guild, member, rank, league=None):
    applied = []

    async def _give(role, reason):
        if role and role not in member.roles:
            try:
                await member.add_roles(role, reason=reason)
                applied.append(role.name)
            except discord.HTTPException:
                pass

    # VERIFIED
    verified_role = _find_role_ci(guild, "VERIFIED") or _find_role_ci(guild, "Verified")
    if verified_role is None:
        verified_role = await get_or_create_role(guild, "VERIFIED", color=discord.Color.green())
    await _give(verified_role, "Verified")
    # Tracker verified
    await _give(_find_role_ci(guild, "Tracker verified"), "Verified (tracker)")
    # Keep the member's rank role in sync with their current selection.
    rank_role = _find_role_ci(guild, VERIFY_RANKS.get(rank, rank))
    for old_rank in VERIFY_RANKS:
        old_role = _find_role_ci(guild, old_rank)
        if old_role and old_role in member.roles and old_role != rank_role:
            try:
                await member.remove_roles(old_role, reason="Verified rank updated")
            except discord.HTTPException:
                pass
    await _give(rank_role, "Verified rank")
    # Keep one current league-eligibility role when a member's rank changes.
    for code in DIVISIONS:
        if code == league:
            continue
        old_role = _find_eligible_role(guild, code)
        if old_role and old_role in member.roles:
            try:
                await member.remove_roles(old_role, reason="League eligibility updated")
            except discord.HTTPException:
                pass
    # League eligible role
    if league:
        await _give(_find_eligible_role(guild, league), "League eligible")
    return applied


class VerifyApprovalView(ui.View):
    def __init__(self, member_id, rank, league=None):
        super().__init__(timeout=None)
        self.member_id = member_id
        self.rank = rank
        self.league = league

    async def interaction_check(self, interaction):
        if not can_review_verification(interaction):
            await interaction.response.send_message("Only the configured staff/reviewer roles can decide this.", ephemeral=True)
            return False
        return True

    @ui.button(label="Approve", emoji="\u2705", style=discord.ButtonStyle.success,
               custom_id="ecrl:verify:approve")
    async def approve(self, interaction, _):
        member = interaction.guild.get_member(self.member_id)
        if member is None:
            return await interaction.response.edit_message(content="That member left the server.", view=None)
        pdata = bot.store.players.setdefault(str(self.member_id), {})
        if pdata.get("verification_status") != "pending":
            return await interaction.response.edit_message(
                content="This verification request is no longer pending.", view=None
            )
        if not is_tracker_profile_link(pdata.get("tracker_link", "")):
            return await interaction.response.edit_message(
                content="The saved Tracker profile link is invalid. Ask the member to submit `/verify` again.", view=None
            )
        league = league_for_player(pdata)
        await interaction.response.defer()
        eligibility_role = _find_eligible_role(interaction.guild, league) if league else None
        if league and eligibility_role is None:
            try:
                eligibility_role = await get_or_create_role(
                    interaction.guild,
                    f"{league_display_name(league)} Eligible",
                    color=discord.Color.teal(),
                )
                league_cfg(league)["eligible_role"] = eligibility_role.id
                await bot.store.save()
            except discord.HTTPException:
                return await interaction.followup.send(
                    f"I couldn't create the **{league_display_name(league)} Eligible** role. "
                    "Give the bot Manage Roles and move its role above eligibility roles, then retry approval.",
                    ephemeral=True,
                )
        applied = await _apply_verification(interaction.guild, member, self.rank, league)
        eligibility_role = _find_eligible_role(interaction.guild, league) if league else None
        eligibility_granted = bool(
            not league or (eligibility_role and (
                eligibility_role in member.roles or eligibility_role.name in applied
            ))
        )
        pdata["verified"] = True
        pdata["smurf_flag"] = False
        pdata["verification_status"] = "approved"
        if league:
            pdata["last_division"] = league
        else:
            pdata.pop("last_division", None)
        pdata["verification_approved_by"] = interaction.user.id
        pdata["verification_approved_at"] = datetime.now(timezone.utc).isoformat()
        pdata["eligible_role_granted"] = bool(league and eligibility_granted)
        pdata.pop("verification_message_id", None)
        await bot.store.save()
        role_note = (
            f"League role **{eligibility_role.name}** is ready."
            if eligibility_granted and league
            else "The account is approved, but the bot could not grant the league-eligible role. Check its role permissions and position."
            if league
            else "This MMR is outside the configured league ranges, so no league-eligible role was granted."
        )
        await interaction.edit_original_response(
            content=f"\u2705 Approved {member.mention} — {role_note} (by {interaction.user.mention}).",
            view=None)
        try:
            await member.send(f"\u2705 Your account was reviewed in **{interaction.guild.name}**. {role_note}")
        except discord.HTTPException:
            pass

    @ui.button(label="Reject", emoji="\u274c", style=discord.ButtonStyle.danger,
               custom_id="ecrl:verify:reject")
    async def reject(self, interaction, _):
        pdata = bot.store.players.setdefault(str(self.member_id), {})
        if pdata.get("verification_status") != "pending":
            return await interaction.response.edit_message(
                content="This verification request is no longer pending.", view=None
            )
        await interaction.response.defer()
        member = interaction.guild.get_member(self.member_id)
        if member:
            await _clear_verification_roles(interaction.guild, member)
        pdata["verified"] = False
        pdata["verification_status"] = "rejected"
        pdata.pop("last_division", None)
        pdata.pop("verification_league", None)
        pdata.pop("verification_message_id", None)
        await bot.store.save()
        await interaction.edit_original_response(
            content=f"\U0001f6ab Verification rejected for <@{self.member_id}> (by {interaction.user.mention}).", view=None)
        if member:
            try:
                await member.send(f"\U0001f6ab Your verification in **{interaction.guild.name}** was not approved. Contact staff if this is a mistake.")
            except discord.HTTPException:
                pass


@bot.tree.command(name="verify", description="Submit your Rocket League account for staff verification")
@app_commands.guild_only()
@app_commands.describe(
    user="Your Discord user (admins can submit for another member)",
    rl_username="Your in-game Rocket League username",
    tracker_link="Your Rocket League Tracker Network profile URL",
    mode="Which competitive playlist the MMR belongs to",
    mmr="Your current MMR in that playlist",
    platform="The platform used by the Tracker profile",
)
@app_commands.choices(
    mode=[app_commands.Choice(name=p, value=p) for p in ("3v3", "2v2")],
    platform=[app_commands.Choice(name=p, value=p) for p in ("Epic", "Steam", "PlayStation", "Xbox", "Switch")],
)
async def verify(
    interaction: discord.Interaction,
    user: discord.Member,
    rl_username: str,
    tracker_link: str,
    mode: app_commands.Choice[str],
    mmr: app_commands.Range[int, 0, 5000],
    platform: app_commands.Choice[str],
) -> None:
    if user.id != interaction.user.id and not is_admin(interaction):
        return await interaction.response.send_message(
            "❌ You can only submit a verification for yourself. Staff can submit for another member.",
            ephemeral=True,
        )
    rl_username = rl_username.strip()
    tracker_link = tracker_link.strip()
    if not rl_username:
        return await interaction.response.send_message("❌ Enter your in-game Rocket League username.", ephemeral=True)
    if len(rl_username) > 100:
        return await interaction.response.send_message("❌ The Rocket League username is too long.", ephemeral=True)
    if len(tracker_link) > 500:
        return await interaction.response.send_message("❌ The Tracker profile link is too long.", ephemeral=True)
    if not is_tracker_profile_link(tracker_link):
        return await interaction.response.send_message(
            "❌ Enter a Rocket League Tracker Network profile link, such as `https://rocketleague.tracker.network/rocket-league/profile/...`.",
            ephemeral=True,
        )
    rank_value = f"{mmr} MMR ({mode.value})"
    league_value = league_for_mmr(mmr, mode.value)
    staff_channel = resolve_staff_channel(interaction.guild)
    if staff_channel is None:
        return await interaction.response.send_message(
            "❌ No staff verification channel is configured. Ask an admin to set `signing_approval_channel` with `/config`.",
            ephemeral=True,
        )

    flags = smurf_report(interaction, rl_username, tracker_link, rank_value, user, mmr=mmr)
    await interaction.response.defer(ephemeral=True)
    pdata = bot.store.players.setdefault(str(user.id), {})
    pdata["epic"] = rl_username
    pdata["tracker_link"] = tracker_link
    pdata["rank"] = rank_value
    pdata["mmr"] = mmr
    pdata["playlist"] = mode.value
    pdata["verification_league"] = league_value
    if league_value:
        pdata["last_division"] = league_value
    else:
        pdata.pop("last_division", None)
    pdata["platform"] = platform.value
    pdata["smurf_flag"] = bool(flags)
    pdata["verified"] = False
    pdata["verification_status"] = "pending"
    pdata["eligible_role_granted"] = False
    pdata["verification_submitted_by"] = interaction.user.id
    pdata["verification_submitted_at"] = datetime.now(timezone.utc).isoformat()
    pdata.pop("verification_message_id", None)
    await bot.store.save()
    await _clear_verification_roles(interaction.guild, user)

    league_line = (
        f"**Eligible league:** {league_display_name(league_value)} ({league_value})"
        if league_value else
        "**Eligible league:** MMR is outside the configured ranges"
    )
    embed = discord.Embed(
        title="🛂 Rocket League Verification Request",
        description=f"Review the submitted Tracker profile and confirm that it belongs to {user.mention}.",
        color=discord.Color.orange() if flags else discord.Color.blurple(),
    )
    embed.add_field(name="Discord user", value=f"{user.mention} (`{user.id}`)", inline=False)
    embed.add_field(name="Rocket League username", value=rl_username, inline=True)
    embed.add_field(name="Queue / MMR / platform", value=f"{mode.value} · {mmr} MMR · {platform.value}", inline=True)
    embed.add_field(name="Tracker profile", value=f"[Open Tracker profile]({tracker_link})", inline=False)
    embed.add_field(name="League", value=league_line, inline=True)
    embed.add_field(name="Submitted by", value=interaction.user.mention, inline=True)
    embed.add_field(
        name="Automatic checks",
        value="\n".join(f"• {flag}" for flag in flags) if flags else "No duplicate or account-age flags.",
        inline=False,
    )
    reviewer_role = next(
        (role for wanted in ("head of staff", "staff")
         for role in interaction.guild.roles if _norm(role.name) == wanted),
        None,
    )
    allowed_mentions = discord.AllowedMentions(
        roles=bool(reviewer_role), users=False, everyone=False
    )
    try:
        staff_message = await staff_channel.send(
            content=reviewer_role.mention if reviewer_role else None,
            embed=embed,
            view=VerifyApprovalView(user.id, rank_value, league_value),
            allowed_mentions=allowed_mentions,
        )
    except discord.HTTPException:
        pdata["verification_status"] = "delivery_failed"
        await bot.store.save()
        return await interaction.followup.send(
            "❌ I couldn't send the application to staff. Your roles remain unverified; ask an admin to check the staff channel permissions.",
            ephemeral=True,
        )
    pdata["verification_message_id"] = staff_message.id
    await bot.store.save()
    await interaction.followup.send(
        f"✅ Verification request submitted for {user.mention}. Staff will review the Tracker profile before granting the league-eligible role.",
        ephemeral=True,
    )


# --------------------------------------------------------------------------- #

def main() -> None:
    token = load_token()
    log.info("Starting bot…")
    bot.run(token, log_handler=None)  # logging is configured above


if __name__ == "__main__":
    main()

# The Titan Elites Division Bot

This is a separate bot package configured for the **The Titan Elites Division** Discord server. Its data file starts clean for Season 4 and does not include teams or player records from the other server package.

## Install and start

Use Python 3.12 or newer:

```powershell
py -3.12 -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python bot.py
```

The bot reads `DISCORD_TOKEN` from the process environment or a local `.env` file. The package contains `.env.example` as a template and does not contain or replace `.env`.

Enable the **Server Members Intent** in the Discord Developer Portal. The bot needs Manage Roles and Manage Channels for league setup and team automation. Its role must be placed above the roles it assigns. Manage Messages is needed for replacing old free-agent posts.

## Season 4 MMR leagues

The config uses the league ranges from the supplied season announcement. Endpoints are inclusive, and the queue is part of each league so a 2v2 MMR never selects a 3v3 league.

| Code | League | Queue | MMR |
| --- | --- | --- | ---: |
| SL3 | SSL League | 3v3 | 1900+ |
| CL3 | Champions League | 3v3 | 1600–1899 |
| PL3 | Premier League | 3v3 | 1350–1599 |
| CH3 | Championship League | 3v3 | 1100–1300 |
| TL2 | Titans League | 2v2 | 1900+ |
| LL2 | La Liga League | 2v2 | 1450–1600 |
| SA2 | Seria A League | 2v2 | 1300–1449 |

The source ranges leave 3v3 MMR 1301–1349 and 2v2 MMR 1601–1899 outside a league. The bot preserves those gaps and verifies accounts in that range without granting a league eligibility role. You can change the ranges with `/league-set-mmr`.

Prize pools remain undecided in the source announcement and are not set in the bot. The announcement listed sign-ups for Friday, October 23, 2026; that date has passed, so no future sign-up date is scheduled here.

## Existing server channels

`ecrl_data.json` uses IDs from the server export dated October 25, 2026. It connects the 3v3 SSL, Champions, and Premier boards/fixtures to the existing Nexus, A League, and X League channels, and connects Serie A to the existing 2v2 Europa table and fixtures. Existing free-agent channels are mapped for the two SSL leagues, Champions, and Premier. Other leagues use `#team-signup` until you connect a dedicated channel with `/set-league`.

The Champions and Premier manager roles are mapped to the current GC2–GC3 and C3–GC1 manager roles. The other leagues need a Team Manager role mapping for manager pings.

## First-time server setup

Run `/set-league` once for each league code: `SL3`, `CL3`, `PL3`, `CH3`, `TL2`, `LL2`, and `SA2`. It keeps saved channel/role mappings and creates missing manager, co-manager, eligibility roles, and team categories. If you have a different existing role or channel, select it in the command instead of using the generated one.

For a league without a saved roster or fixtures channel, select the channel through `/set-league`. You can also connect a league free-agent channel there. Without a league-specific free-agent channel, announcements go to `#team-signup`.

## Verification and signings

- `/verify` collects the Discord user, Rocket League username, Tracker profile URL, playlist (`3v3` or `2v2`), MMR, and platform. Staff review the Tracker profile before approval. Approval assigns the correct eligible role for that queue and MMR range. The bot checks duplicate usernames/profiles and account-age risks.
- `/sign` sends a roster offer to the selected player's DMs. The player must have the eligible role for that exact league before an offer is sent and again before roster placement.
- `/join`, transfers, and admin roster additions apply the same eligibility check.
- Free-agent announcements include the player's playlist, MMR, and league. They require the matching eligible role and ping the mapped Team Manager role.
- `/profile` shows the saved Tracker profile, queue, MMR, league, and verification status.

If a free-agent announcement should ping a specific manager role, connect it with `/set-league` or select the role when the league is created. The server export did not contain a separate manager role for every new Season 4 league.

## League changes and commands

- `/league-list` shows current names, queues, MMR ranges, and channel mappings.
- `/league-create-mmr` creates a new queue-specific league and its roles/category.
- `/league-set-mmr` changes a league's queue or MMR range. Overlapping ranges in the same queue are rejected.
- `/league-rename old_code new_code new_name` changes the league code and optional public name while carrying over saved channel and role IDs. Rename the visible Discord roles/categories separately if desired.
- `/set-league` connects existing channels and roles or creates missing setup resources.

Sponsors can change league names without changing their MMR range. Admins can use `/league-rename` with a new public name after the sponsor is confirmed.

## Match channels and data

The package is configured for Season 4 and starts with empty teams, players, and matches. The supplied server export lists roles and channels, but does not provide a complete team roster, so the bot will not import or invent player data. Set the match room and archive categories with `/config` if you want private match channels.

The bot also has `/schedule`, `/report-result`, `/confirm-result`, `/standings`, `/fixtures`, `/stats`, `/dashboard`, and `/announce-free-agents` for the regular league workflow. Run `/help` in Discord for the full command list.


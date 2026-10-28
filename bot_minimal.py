import discord
from discord import app_commands, ui
import os
import json
from datetime import datetime
from typing import Optional, List

# ====================== CONFIG ======================
DATA_FILE = "ecrl_data.json"
TEAMS_CATEGORY_NAME = "TEAMS"

def load_data():
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except:
            pass
    return {"teams": {}, "players": {}}

def save_data(data):
    with open(DATA_FILE, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2)

# Load token from .env
try:
    with open('.env', 'r', encoding='utf-8') as f:
        for line in f:
            if line.startswith('DISCORD_TOKEN='):
                TOKEN = line.split('=', 1)[1].strip()
                print("✅ Token loaded successfully")
                break
except:
    TOKEN = None

if not TOKEN:
    print("❌ DISCORD_TOKEN not found in .env file")
    exit()

class ECRLBot(discord.Client):
    def __init__(self):
        intents = discord.Intents.all()
        super().__init__(intents=intents)
        self.tree = app_commands.CommandTree(self)
        self.data = load_data()

    async def setup_hook(self):
        await self.tree.sync()
        print("✅ Slash commands synced to Discord")

    async def on_ready(self):
        print(f"🚀 MINIMAL ECRL BOT IS ONLINE as {self.user}")
        activity = discord.Activity(type=discord.ActivityType.competing, name="ECRL Testing")
        await self.change_presence(status=discord.Status.online, activity=activity)

bot = ECRLBot()

def is_admin(interaction: discord.Interaction):
    roles = [r.name.lower() for r in interaction.user.roles]
    return any("admin" in n or "owner" in n or "co-owner" in n for n in roles)

# ====================== VIEWS ======================
class TicketView(ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @ui.button(label="🎫 Open Ticket", style=discord.ButtonStyle.green)
    async def open_ticket(self, interaction: discord.Interaction, button: ui.Button):
        guild = interaction.guild
        category = discord.utils.get(guild.categories, name="Tickets") or await guild.create_category("Tickets")
        overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            interaction.user: discord.PermissionOverwrite(view_channel=True, send_messages=True)
        }
        for role in guild.roles:
            if any(x in role.name.lower() for x in ["admin", "staff", "moderator"]):
                overwrites[role] = discord.PermissionOverwrite(view_channel=True, send_messages=True)
        channel = await guild.create_text_channel(f"ticket-{interaction.user.name}", category=category, overwrites=overwrites)
        await channel.send(f"🎫 New ticket opened by {interaction.user.mention}")
        await interaction.response.send_message(f"✅ Ticket created: {channel.mention}", ephemeral=True)

class CustomTicketModal(ui.Modal):
    def __init__(self, title: str, questions: List[str]):
        super().__init__(title=title)
        self.questions = questions
        for i, q in enumerate(questions[:5]):
            self.add_item(ui.TextInput(label=q, style=discord.TextStyle.paragraph, required=True))

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.send_message("✅ Your custom ticket has been submitted!", ephemeral=True)

class CustomTicketView(ui.View):
    def __init__(self, title, desc, questions):
        super().__init__(timeout=None)
        self.title = title
        self.questions = questions

    @ui.button(label="📩 Submit Custom Ticket", style=discord.ButtonStyle.primary)
    async def open(self, interaction: discord.Interaction, button: ui.Button):
        await interaction.response.send_modal(CustomTicketModal(self.title, self.questions))

# Delete Team (only from TEAMS category)
class TeamSelect(ui.Select):
    def __init__(self, teams):
        options = [discord.SelectOption(label=t, value=t) for t in teams[:25]]
        super().__init__(placeholder="Select team to delete", options=options)

    async def callback(self, interaction: discord.Interaction):
        view = DeleteConfirmView(self.values[0], interaction)
        await interaction.response.send_message(f"⚠️ Confirm delete **{self.values[0]}**?", view=view, ephemeral=True)

class DeleteTeamView(ui.View):
    def __init__(self, teams):
        super().__init__()
        self.add_item(TeamSelect(teams))

class DeleteConfirmView(ui.View):
    def __init__(self, team_name, orig):
        super().__init__(timeout=60)
        self.team_name = team_name
        self.orig = orig

    @ui.button(label="✅ YES, DELETE", style=discord.ButtonStyle.red)
    async def confirm(self, interaction: discord.Interaction, button: ui.Button):
        if interaction.user.id != self.orig.user.id:
            return await interaction.response.send_message("❌ Only the person who started this can confirm.", ephemeral=True)
        guild = interaction.guild
        safe = self.team_name.lower().replace(" ", "-")
        deleted = []
        teams_cat = discord.utils.get(guild.categories, name=TEAMS_CATEGORY_NAME)
        if teams_cat:
            for ch in teams_cat.channels:
                if safe in ch.name:
                    await ch.delete()
                    deleted.append(ch.name)
        role = discord.utils.get(guild.roles, name=self.team_name)
        if role:
            await role.delete()
            deleted.append("Role")
        if self.team_name in bot.data.get("teams", {}):
            del bot.data["teams"][self.team_name]
            save_data(bot.data)
        await interaction.response.send_message(f"💥 Deleted: {', '.join(deleted)}", ephemeral=True)
        self.stop()

    @ui.button(label="❌ CANCEL", style=discord.ButtonStyle.gray)
    async def cancel(self, interaction: discord.Interaction, button: ui.Button):
        await interaction.response.send_message("Cancelled.", ephemeral=True)
        self.stop()

# ====================== COMMANDS (Only 8 total) ======================
@bot.tree.command(name="setup-buttons", description="Post the ticket panel (Admin only)")
async def setup_buttons(interaction: discord.Interaction):
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only!", ephemeral=True)
    embed = discord.Embed(title="ECRL Hub", description="Choose an option below", color=discord.Color.purple())
    await interaction.channel.send(embed=embed, view=TicketView())
    await interaction.response.send_message("✅ Panel posted!", ephemeral=True)

@bot.tree.command(name="create-team", description="Create a new team with channels and roles (Admin only)")
@app_commands.choices(division=[app_commands.Choice(name=d, value=d) for d in ["EL", "PD", "CD", "L1", "L2", "ACADEMY"]])
async def create_team(interaction: discord.Interaction, team_name: str, manager: discord.Member, division: app_commands.Choice[str]):
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only!", ephemeral=True)
    guild = interaction.guild
    safe_name = team_name.lower().replace(" ", "-")
    teams_cat = discord.utils.get(guild.categories, name=TEAMS_CATEGORY_NAME) or await guild.create_category(TEAMS_CATEGORY_NAME)
    team_role = await guild.create_role(name=team_name, color=discord.Color.blue(), mentionable=True)
    mgr_role_name = f"👔 Team Manager ({division.value})"
    mgr_role = discord.utils.get(guild.roles, name=mgr_role_name) or await guild.create_role(name=mgr_role_name, color=discord.Color.gold())
    await manager.add_roles(team_role, mgr_role)
    ow = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        team_role: discord.PermissionOverwrite(view_channel=True, send_messages=True, connect=True),
        mgr_role: discord.PermissionOverwrite(view_channel=True, send_messages=True, manage_channels=True)
    }
    text = await guild.create_text_channel(f"{safe_name}-talking", category=teams_cat, overwrites=ow)
    voice = await guild.create_voice_channel(f"{safe_name}-vc", category=teams_cat, overwrites=ow)
    bot.data["teams"][team_name] = {"manager": manager.id, "division": division.value, "roster": [manager.id]}
    save_data(bot.data)
    await interaction.response.send_message(f"🏆 **{team_name}** created in division {division.value}!")

@bot.tree.command(name="delete-team", description="Delete a team using dropdown (Admin only)")
async def delete_team(interaction: discord.Interaction):
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only!", ephemeral=True)
    teams = []
    teams_cat = discord.utils.get(interaction.guild.categories, name=TEAMS_CATEGORY_NAME)
    if teams_cat:
        for ch in teams_cat.channels:
            if ch.name.endswith("-talking"):
                name = ch.name.replace("-talking", "").replace("-", " ").title()
                if name not in teams:
                    teams.append(name)
    if not teams:
        return await interaction.response.send_message("No teams found in TEAMS category yet.", ephemeral=True)
    await interaction.response.send_message("🗑️ Select a team to delete:", view=DeleteTeamView(teams), ephemeral=True)

@bot.tree.command(name="create-custom-ticket", description="Create a custom ticket panel with your questions (Admin only)")
async def create_custom_ticket(interaction: discord.Interaction, title: str, description: str, q1: str, q2: str = "", q3: str = ""):
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only!", ephemeral=True)
    questions = [q for q in [q1, q2, q3] if q.strip()]
    embed = discord.Embed(title=title, description=description, color=discord.Color.blue())
    await interaction.channel.send(embed=embed, view=CustomTicketView(title, description, questions))
    await interaction.response.send_message("✅ Custom ticket panel posted!", ephemeral=True)

@bot.tree.command(name="ping", description="Check if the bot is online")
async def ping(interaction: discord.Interaction):
    await interaction.response.send_message(f"✅ ECRL Minimal Bot is ONLINE | Members: {interaction.guild.member_count}")

@bot.tree.command(name="sync", description="Force refresh all slash commands (Admin only)")
async def force_sync(interaction: discord.Interaction):
    if not is_admin(interaction):
        return await interaction.response.send_message("❌ Admin only!", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    try:
        await bot.tree.sync(guild=interaction.guild)
        await interaction.followup.send("✅ Commands synced! Type `/` again in 15 seconds.", ephemeral=True)
    except Exception as e:
        await interaction.followup.send(f"❌ Sync error: {e}", ephemeral=True)

@bot.tree.command(name="register", description="Link your Epic Games ID")
async def register(interaction: discord.Interaction, epic_id: str):
    bot.data.setdefault("players", {})[str(interaction.user.id)] = {"epic": epic_id}
    save_data(bot.data)
    await interaction.response.send_message(f"✅ Registered with Epic ID: **{epic_id}**")

@bot.tree.command(name="profile", description="View profile and linked Epic ID")
async def profile(interaction: discord.Interaction, user: Optional[discord.Member] = None):
    user = user or interaction.user
    pdata = bot.data.get("players", {}).get(str(user.id), {})
    await interaction.response.send_message(f"📋 {user.mention} | Epic ID: {pdata.get('epic', 'Not linked yet')}")

print("✅ Minimal bot ready with only 8 commands. Run it and use /sync")
bot.run(TOKEN)
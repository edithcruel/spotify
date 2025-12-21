local Ffi = require("ffi")
local Vector = require("vector")
local Pui = require("gamesense/pui")
local Http = require('gamesense/http')

local AccentColor = Pui.reference("misc", "settings", "menu color").value
local AccentHex = string.format("%02x%02x%02x%02x", AccentColor[1], AccentColor[2], AccentColor[3], 255)

local UiNewCheckbox = ui.new_checkbox
local UiNewLabel = ui.new_label
local UiNewMultiselect = ui.new_multiselect
local UiReference = ui.reference
local UiSetVisible = ui.set_visible
local UiSetEnabled = ui.set_enabled
local UiSetCallback = ui.set_callback
local UiGet = ui.get

local EntityGetLocalPlayer = entity.get_local_player
local EntityIsAlive = entity.is_alive
local EntityGetPlayers = entity.get_players
local EntityGetProp = entity.get_prop
local EntityGetPlayerName = entity.get_player_name
local EntityIsEnemy = entity.is_enemy
local EntityGetPlayerWeapon = entity.get_player_weapon

local GlobalsTickCount = globals.tickcount
local GlobalsCurTime = globals.curtime
local GlobalsTickInterval = globals.tickinterval

local ClientSetEventCallback = client.set_event_callback
local ClientDelayCall = client.delay_call
local ClientScreenSize = client.screen_size
local ClientUserIdToEntIndex = client.userid_to_entindex
local ClientColorLog = client.color_log
local ClientRandomInt = client.random_int
local ClientExec = client.exec
local ClientRealLatency = client.real_latency

local RendererText = renderer.text
local RendererLine = renderer.line
local RendererCircle = renderer.circle
local RendererMeasureText = renderer.measure_text

local PlistSet = plist.set
local Weapons = require("gamesense/csgo_weapons")

local ar, ag, ab = Pui.reference('misc', 'settings', 'menu color').value[1], Pui.reference('misc', 'settings', 'menu color').value[2], Pui.reference('misc', 'settings', 'menu color').value[3]
local AssemblyUserData = ASSEMBLY_USER_DATA or { username = "klych", role = "lezhal" }
local Username = AssemblyUserData.username
local UserRole = AssemblyUserData.role

if type(AssemblyUserData) ~= "table" or not Username or not UserRole then
    error("Access denied. Invalid user data.")
end

if not ({LIVE = true, BACKSTAGE = true, DEVELOPER = true})[UserRole] then
    error("Access denied. Invalid role: " .. tostring(UserRole))
end

local Version = "revamp"
local Build, BuildLevel, IsLive, IsBackstage, IsDeveloper = "enhanced", 1, false, false, false

local Builds = {
    LIVE = {1, "live"},
    BACKSTAGE = {2, "backstage"},
    DEVELOPER = {3, "developer"}
}

local CurrentBuild = Builds[UserRole] or Builds.LIVE
Build, BuildLevel = CurrentBuild[2], CurrentBuild[1]

if BuildLevel >= 1 then IsLive = true end
if BuildLevel >= 2 then IsBackstage = true end
if BuildLevel >= 3 then IsDeveloper = true end

Ffi.cdef [[
    typedef struct {
        char pad[0x78];
        float eye_yaw;
        float eye_pitch;
        float goal_feet_yaw;
        float current_feet_yaw;
        float current_torso_yaw;
        char pad2[0x4C];
        float duck_amount;
        bool on_ground;
        char pad3[0x7];
        float velocity;
        float up_velocity;
        float speed_normalized;
        float feet_speed_forward_side;
        float time_since_started_moving;
        float time_since_stopped_moving;
        char pad4[0x8];
        float last_origin_z;
        char pad5[0x7C];
        float max_yaw;
        float min_yaw;
    } animstate_t;
    typedef void*(__thiscall* get_client_entity_t)(void*, int);
]]

local ClassPtr = Ffi.typeof("void***")
local EntityList = client.create_interface("client.dll", "VClientEntityList003")
local EntityListPtr = Ffi.cast(ClassPtr, EntityList)
local GetClientEntity = Ffi.cast("get_client_entity_t", EntityListPtr[0][3])

local function GetAnimstate(playerIndex)
    local entityPtr = GetClientEntity(EntityListPtr, playerIndex)
    if entityPtr == nil then
        return nil
    end
    return Ffi.cast("animstate_t**", Ffi.cast("char*", entityPtr) + 0x9960)[0]
end

local function CreateVector3(x, y, z)
    return { x = x or 0, y = y or 0, z = z or 0 }
end

local function TicksToTime(ticks)
    return GlobalsTickInterval() * ticks
end

local RefNames = {
    "Add to whitelist",
    "Allow shared ESP updates",
    "Disable visuals",
    "High priority",
    "Force pitch",
    "Force body yaw",
    "Correction active",
    "Override prefer body aim",
    "Override safe point",
    "Apply to all"
}

local RbfxRefs = {
    dt = { UiReference("RAGE", "Aimbot", "Double tap") },
    hideShots = { UiReference("AA", "Other", "On shot anti-aim") },
    aimbot = UiReference("RAGE", "Aimbot", "Enabled"),
    correction = UiReference("RAGE", "Other", "Anti-aim correction")
}

local GameSensePList = {
    adjustments = {
        gsAddToWhitelist = UiReference("Players", "Adjustments", "Add to whitelist"),
        gsAllowSharedEsp = UiReference("Players", "Adjustments", "Allow shared ESP updates"),
        gsDisableVisuals = UiReference("Players", "Adjustments", "Disable visuals"),
        gsHighPriority = UiReference("Players", "Adjustments", "High priority"),
        gsForcePitch = UiReference("Players", "Adjustments", "Force pitch"),
        gsForceBodyYaw = UiReference("Players", "Adjustments", "Force body yaw"),
        gsCorrectionActive = UiReference("Players", "Adjustments", "Correction active"),
        gsOverridePreferBodyAim = UiReference("Players", "Adjustments", "Override prefer body aim"),
        gsOverrideSafePoint = UiReference("Players", "Adjustments", "Override safe point"),
        gsApplyToAll = UiReference("Players", "Adjustments", "Apply to all"),
    }
}

for _, propName in ipairs(RefNames) do
    local ref = UiReference("Players", "Adjustments", propName)
    if ref then
        UiSetVisible(ref, false)
    end
end

local forceBodyYawValueRef = UiReference("Players", "Adjustments", "Force body yaw value")
if forceBodyYawValueRef then
    UiSetVisible(forceBodyYawValueRef, false)
end

local function HasOption(multiselectRef, keyword)
    local list = UiGet(multiselectRef)
    if not list then
        return false
    end
    for _, item in ipairs(list) do
        if item:find(keyword, 1, true) then
            return true
        end
    end
    return false
end

local RechargeTimer = GlobalsTickCount()
local ScriptLeakStop = 14
local CorrectionCache = nil

local Net = {
    flags = 260,
    sequence = 10412,
    cycle = 10408,
    playbackRate = 10416,
    seqStartTime = 10420,
    sequenceFinished = 10424
}

local function SyncAnim(entPtr)
    mem.write(entPtr + Net.sequence, 0, "int")
    mem.write(entPtr + Net.cycle, 0, "float")
    mem.write(entPtr + Net.playbackRate, 1, "float")
    mem.write(entPtr + Net.seqStartTime, 0, "float")
    mem.write(entPtr + Net.sequenceFinished, false, "bool")
end

local UiElements = {}
UiElements.enabled = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "$ Assembly \aFFFFFFFF" .. Build)
UiElements.divider2 = UiNewLabel("Players", "Adjustments", "\a37373750‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾")

UiElements.correction = UiNewMultiselect(
    "Players",
    "Adjustments",
    "\a" .. AccentHex .. " \aFFFFFFFFCorrection Types",
    {
        "\a" .. AccentHex .. " \aFFFFFFFFJitter",
        "\a" .. AccentHex .. " \aFFFFFFFFDesync",
        "\a" .. AccentHex .. " \aFFFFFFFFAnimstate",
        "\a" .. AccentHex .. " \aFFFFFFFFDefensive"
    }
)
UiElements.labeladfs = UiNewLabel("Players", "Adjustments", "\aFFFFFF00")
UiElements.advanced = UiNewMultiselect(
    "Players",
    "Adjustments",
    "\a" .. AccentHex .. " \aFFFFFFFFAdvanced Options",
    {
        "\a" .. AccentHex .. " \aFFFFFFFFScales",
        "\a" .. AccentHex .. " \aFFFFFFFFScanner",
        "\a" .. AccentHex .. " \aFFFFFFFFBruteforce"
    }
)
UiElements.labeladf = UiNewLabel("Players", "Adjustments", "\aFFFFFF00")

UiElements.divider2d3 = UiNewLabel("Players", "Adjustments", "\a37373750‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾")

UiElements.rageFix = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "</>  \aFFFFFFFFRagebot Fix")
UiElements.animSync = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "⇄ \aFFFFFFFFAnimation Sync")
UiElements.hitRate = UiNewCheckbox("Players", "Adjustments", "% Hitrate Visualization")-- UiElements.hitRate = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "% \aFFFFFFFFHitrate Visualization")
UiElements.trashTalk = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "  \aFFFFFFFFKill Say")
UiElements.kirkMode = UiNewCheckbox("Players", "Adjustments", "K  Kirk Mode") 
UiElements.clanTag = UiNewCheckbox("Players", "Adjustments", " Clan Tag")-- UiElements.clanTag = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. " \aFFFFFFFFClan Tag")
UiElements.hitMarker = UiNewCheckbox("Players", "Adjustments", "⊹ Hitmarker")-- UiElements.hitMarker = UiNewCheckbox("Players", "Adjustments", "\a" .. AccentHex .. "⊹ \aFFFFFFFFHitmarker")
UiElements.labeladf2 = UiNewLabel("Players", "Adjustments", "\aFFFFFF00")

UiElements.divider23 = UiNewLabel("Players", "Adjustments", "\a37373750‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾")
UiElements.footerLabel = UiNewLabel("Players", "Adjustments", "\aFFFFFF15  ₊✩‧₊˚౨ৎ˚₊✩‧₊ @assemblygs ₊✩‧₊˚౨ৎ˚₊˚⟡˖…")

local function UpdateVisibility()
    local enabled = UiGet(UiElements.enabled)
    
    UiSetVisible(UiElements.enabled, true)
    UiSetVisible(UiElements.divider2, enabled)
    UiSetVisible(UiElements.divider23, enabled)
    UiSetVisible(UiElements.divider2d3, enabled)
    UiSetVisible(UiElements.labeladf, enabled)
    UiSetVisible(UiElements.labeladfs, enabled)
    UiSetVisible(UiElements.hitRate, enabled)
    UiSetVisible(UiElements.clanTag, enabled)
    UiSetVisible(UiElements.correction, enabled)
    UiSetVisible(UiElements.advanced, enabled)
    UiSetVisible(UiElements.trashTalk, enabled)
    UiSetVisible(UiElements.hitMarker, enabled)
    UiSetVisible(UiElements.animSync, enabled)
    UiSetVisible(UiElements.footerLabel, enabled)
    UiSetVisible(UiElements.kirkMode, enabled)
    UiSetVisible(UiElements.rageFix, enabled)
end

UpdateVisibility()
UiSetCallback(UiElements.enabled, UpdateVisibility)

local function NormalizeAngle(angle)
    while angle > 180 do
        angle = angle - 360
    end
    while angle < -180 do
        angle = angle + 360
    end
    return angle
end

local function AngleDifference(a, b)
    return NormalizeAngle(a - b)
end

local function Clamp(value, min, max)
    if value < min then
        return min
    end
    if value > max then
        return max
    end
    return value
end

local function GetAbsAngleDifference(a, b)
    local diff = math.abs(AngleDifference(a, b))
    return diff > 180 and 360 - diff or diff
end

local function IsDefensivePitch(pitch)
    return math.abs(pitch + 180) < 10 or math.abs(pitch) < 10 or math.abs(pitch - 180) < 10 or 
           math.abs(pitch - 89) < 10 or math.abs(pitch + 89) < 10
end

local DefensiveData = {}

local function ResolveDefensive(player)
    if not player or not entity.is_alive(player) then
        return false
    end
    
    local playerId = entity.get_prop(player, "m_iIndex")
    if playerId <= 0 then return false end
    
    local simTime = entity.get_prop(player, "m_flSimulationTime") or 0
    local eyeAngles = {entity.get_prop(player, "m_angEyeAngles")}
    local eyeYaw = eyeAngles[2] or 0
    local lby = entity.get_prop(player, "m_flLowerBodyYawTarget") or 0
    local flags = entity.get_prop(player, "m_fFlags") or 0
    local onGround = bit.band(flags, 1) ~= 0
    
    local data = DefensiveData[playerId] or {
        History = {},
        LastSimulationTime = 0,
        LastValidSimulationTime = 0,
        IsLocked = false,
        LockStartTick = 0,
        ResolvedDesync = 0,
        ResolvedPitch = 0,
        ValidTickCount = 0
    }
    DefensiveData[playerId] = data
    
    if simTime <= 0.1 then
        data.History = {}
        data.IsLocked = false
        data.ResolvedDesync = 0
        return false
    end
    
    local isBreaking = false
    if onGround then
        local yawDiff = GetAbsAngleDifference(eyeYaw, lby)
        isBreaking = yawDiff > 35 and yawDiff < 145
    end
    
    local deltaTime = simTime - data.LastSimulationTime
    local tickInterval = globals.tickinterval()
    local isValidTick = deltaTime > 0 and math.abs(deltaTime - tickInterval) < 0.001
    
    data.LastSimulationTime = simTime
    
    if isValidTick then
        data.LastValidSimulationTime = simTime
        data.ValidTickCount = data.ValidTickCount + 1
        
        table.insert(data.History, {
            SimTime = simTime,
            EyeYaw = eyeYaw,
            Lby = lby,
            Breaking = isBreaking,
            OnGround = onGround,
            Pitch = eyeAngles[1] or 0
        })
        
        if #data.History > 64 then table.remove(data.History, 1) end
    end
    
    if #data.History >= 8 and not data.IsLocked then
        for i = #data.History - 2, 1, -1 do
            if i + 2 > #data.History then break end
            
            local r1 = data.History[i]
            local r2 = data.History[i+1]
            local r3 = data.History[i+2]
            
            if r1.Breaking and not r2.Breaking and r3.Breaking then
                local diff1 = r2.SimTime - r1.SimTime
                local diff2 = r3.SimTime - r2.SimTime
                
                if diff1 > 0 and diff2 > 0 and diff1 < 0.5 and diff2 < 0.5 then
                    data.IsLocked = true
                    data.LockStartTick = globals.tickcount()
                    data.ResolvedDesync = AngleDifference(r2.Lby, r2.EyeYaw)  -- ~
                    data.ResolvedPitch = r2.Pitch
                    break
                end
            end
        end
    end
    
    if data.IsLocked then
        local ticksLocked = globals.tickcount() - data.LockStartTick
        if ticksLocked > 256 or 
           (isBreaking and ticksLocked > 16) or
           (simTime - data.LastValidSimulationTime > 1.0) then
            data.IsLocked = false
            data.ResolvedDesync = 0
        end
    end
    
    if data.IsLocked and data.ResolvedDesync ~= 0 then
        plist.set(playerId, "Force body yaw", true)
        plist.set(playerId, "Force body yaw value", data.ResolvedDesync)
        
        if IsDefensivePitch(data.ResolvedPitch) then
            local normPitch = (data.ResolvedPitch + 90) / 180
            normPitch = math.max(0, math.min(1, normPitch))
            entity.set_prop(player, "m_flPoseParameter[12]", normPitch)
        end
        
        return true
    else
        plist.set(playerId, "Force body yaw", false)
        return false
    end
end

local LogSystem = {enabled = true}

local function GetBacktrackTicks(player)
    local simTime = EntityGetProp(player, "m_flSimulationTime") or 0
    return math.floor((GlobalsCurTime() - simTime) / GlobalsTickInterval())
end

function LogSystem.addHit(target, damage, hitgroup, confidence, backtrack)
    local playerName = EntityGetPlayerName(target) or "Unknown"
    local hp = EntityGetProp(target, "m_iHealth") or 100
    local hitgroupNames = {
        [1] = "head",
        [2] = "chest",
        [3] = "stomach",
        [4] = "left arm",
        [5] = "right arm",
        [6] = "left leg",
        [7] = "right leg"
    }
    local hitgroupStr = hitgroupNames[hitgroup] or "body"
    
    ClientColorLog(255, 255, 255, "[\0") 
    ClientColorLog(AccentColor[1], AccentColor[2], AccentColor[3], "assembly-" .. Build .. "\0")
    ClientColorLog(255, 255, 255, "] \0") 
    ClientColorLog(255, 255, 255, "Hit \0")
    ClientColorLog(AccentColor[1], AccentColor[2], AccentColor[3], playerName .. " \0")
    ClientColorLog(255, 255, 255, "in the \0") 
    ClientColorLog(AccentColor[1], AccentColor[2], AccentColor[3], hitgroupStr .. " \0")
    ClientColorLog(255, 255, 255, "for \0") 
    ClientColorLog(AccentColor[1], AccentColor[2], AccentColor[3], damage .. " \0")
    ClientColorLog(255, 255, 255, "damage\0") 
    ClientColorLog(171, 171, 171, " (remaining hp: " .. hp .. ", conf: " .. math.floor(confidence * 100) .. "%, bt: 5OO $$$)")-- .. backtrack .. ")"
end

function LogSystem.addMiss(target, reason, confidence, backtrack)
    local playerName = EntityGetPlayerName(target) or "Unknown"
    local simpleReason = (reason == "?" or reason == "unknown") and "resolver" or reason
    
    ClientColorLog(255, 255, 255, "[\0") 
    ClientColorLog(AccentColor[1], AccentColor[2], AccentColor[3], "assembly-" .. Build .. "\0")
    ClientColorLog(255, 255, 255, "] \0") 
    ClientColorLog(255, 255, 255, "Missed \0") 
    ClientColorLog(255, 82, 82, playerName .. " \0")
    ClientColorLog(255, 255, 255, "due to \0") 
    ClientColorLog(255, 82, 82, simpleReason .. " \0")
    ClientColorLog(171, 171, 171, "(conf: " .. math.floor(confidence * 100) .. "%, bt: 5OO $$$)")-- .. backtrack .. ")")
end

local KillSay = {
    phrases = {
        "de 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿 veur Gamesense is bijgewerk niggas. NEET KLAAR VEUR NOG MEER ASS FUCKING",
        "maak uchzelf veur kinder, velure ging nao de publieke pagina I'LL FUCK YOU ALL mit 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿",
        "dich neuke 0 winrate hónd maak dich klaor ik gaon",
        "de 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿 heeft een update gekregen dus je kunt mijn lul gewoon in je kont stoppen",
        "ja ik hoor je wel 20 winrate-hond, slik het maar gewoon in @𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆𝗴𝘀",
        "verdomme is het niet vreemd dat 𝗴𝗼𝗮𝘁𝗲𝗱 je net heeft genaaid @𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆𝗴𝘀?",
        "waardeloze server, je hebt lag, ga jezelf van kant maken, man. Ik ben gewoon een 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿 gebruiker",
        "de build van assembly " .. Build .. " is zo goed, je moet hem echt eens proberen",
        "𝗴𝗼𝗮𝘁𝗲𝗱 won een toernooi van 200 euro met 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿",
        "lol 𝟏 waardeloze hond je bent zo zielig, ik lach me rot",
        "𝗴𝗼𝗮𝘁𝗲𝗱 𝘅 𝘃𝗮𝗻𝗰𝗵𝗲𝘇 maakt alles kapot met 𝗮𝘀𝘀𝗲𝗺𝗯𝗹𝘆 𝗿𝗲𝘀𝗼𝗹𝘃𝗲𝗿. Een hond met een winrate van 20? Zielig dog."
    }
}

function KillSay.send()
    if not UiGet(UiElements.trashTalk) then
        return
    end
    local phrase = KillSay.phrases[ClientRandomInt(1, #KillSay.phrases)]
    ClientExec("say " .. phrase)
end

local Resolver = {
    players = {},
    lastUpdate = 0,
    updateInterval = 1
}

function Resolver.initPlayer(playerIndex)
    if not Resolver.players[playerIndex] then
        Resolver.players[playerIndex] = {
            angleHistory = {},
            lbyHistory = {},
            state = {moving = false, crouching = false, airborne = false},
            resolverData = {side = 0, confidence = 0.5, lastResolved = 0}
        }
    end
    return Resolver.players[playerIndex]
end

function Resolver.detectJitter(playerIndex, currentYaw)
    local data = Resolver.initPlayer(playerIndex)
    table.insert(data.angleHistory, {yaw = currentYaw, time = GlobalsCurTime()})
    if #data.angleHistory > 6 then
        table.remove(data.angleHistory, 1)
    end
    if #data.angleHistory < 3 then
        return false, 0
    end
    local maxDiff = 0
    for i = 2, #data.angleHistory do
        local diff = math.abs(AngleDifference(data.angleHistory[i].yaw, data.angleHistory[i - 1].yaw))
        maxDiff = math.max(maxDiff, diff)
    end
    return maxDiff > 45, Clamp(maxDiff / 90, 0, 1)
end

function Resolver.predictLby(playerIndex, animstate)
    if not animstate then
        return 0, 0
    end
    local data = Resolver.initPlayer(playerIndex)
    local currentLby = animstate.goal_feet_yaw
    table.insert(data.lbyHistory, {value = currentLby, time = GlobalsCurTime()})
    if #data.lbyHistory > 3 then
        table.remove(data.lbyHistory, 1)
    end
    if #data.lbyHistory < 2 then
        return currentLby, 0.1
    end
    local lastChange = math.abs(AngleDifference(data.lbyHistory[#data.lbyHistory].value, data.lbyHistory[#data.lbyHistory - 1].value))
    if lastChange > 60 then
        local direction = (AngleDifference(data.lbyHistory[#data.lbyHistory].value, data.lbyHistory[#data.lbyHistory - 1].value) > 0) and 1 or -1
        return currentLby + (58 * direction), 0.8
    end
    return currentLby, 0.3
end

function Resolver.calculateFreestanding(playerIndex)
    local localPlayer = EntityGetLocalPlayer()
    if not localPlayer then
        return 0, 0
    end
    local enemyOrigin = {EntityGetProp(playerIndex, "m_vecOrigin")}
    local localOrigin = {EntityGetProp(localPlayer, "m_vecOrigin")}
    if not enemyOrigin or not localOrigin then
        return 0, 0
    end
    local dx = localOrigin[1] - enemyOrigin[1]
    local dy = localOrigin[2] - enemyOrigin[2]
    local dist = math.sqrt(dx * dx + dy * dy)
    if dist < 50 then
        return 0, 0
    end
    local angleToLocal = math.deg(math.atan2(dy, dx))
    local eyeYaw = EntityGetProp(playerIndex, "m_angEyeAngles[1]") or 0
    local leftDot = math.cos(math.rad(angleToLocal - (eyeYaw - 90)))
    local rightDot = math.cos(math.rad(angleToLocal - (eyeYaw + 90)))
    return (leftDot > rightDot) and -1 or 1, math.max(math.abs(leftDot), math.abs(rightDot))
end

function Resolver.getPlayerState(playerIndex)
    local data = Resolver.initPlayer(playerIndex)
    local velocity = {EntityGetProp(playerIndex, "m_vecVelocity")}
    local vx, vy = velocity[1] or 0, velocity[2] or 0
    local speed = math.sqrt(vx * vx + vy * vy)
    local flags = EntityGetProp(playerIndex, "m_fFlags") or 0
    local onGround = bit.band(flags, 1) == 1
    local duckAmount = EntityGetProp(playerIndex, "m_flDuckAmount") or 0
    data.state.moving = speed > 5
    data.state.crouching = duckAmount > 0.5
    data.state.airborne = not onGround
    return data.state
end

function Resolver.resolve(playerIndex)
    if not UiGet(UiElements.enabled) then
        return
    end

    local playerId = EntityGetProp(playerIndex, "m_iIndex")
    if not playerId or playerId <= 0 then
        return
    end

    if HasOption(UiElements.correction, "Defensive Resolver") then
        local defensiveActive = ResolveDefensive(playerIndex)
        if defensiveActive then
            return
        end
    end

    local data = Resolver.initPlayer(playerIndex)
    local animstate = GetAnimstate(playerIndex)
    if not animstate then
        return
    end

    local eyeYaw = animstate.eye_yaw
    local maxDesync = animstate.max_yaw or 58
    local playerState = Resolver.getPlayerState(playerIndex)

    local features = {}
    if HasOption(UiElements.correction, "Jitter Resolver") then
        local isJittering, jitterConf = Resolver.detectJitter(playerIndex, eyeYaw)
        features.jitter = jitterConf
    else
        features.jitter = 0
    end

    if HasOption(UiElements.correction, "Desync Resolver") then
        local lbyAngle, lbyConf = Resolver.predictLby(playerIndex, animstate)
        features.lby = lbyConf
    else
        features.lby = 0
    end

    if HasOption(UiElements.advanced, "Layer-6 Scan") then
        local layer6 = EntityGetProp(playerIndex, "m_flPoseParameter", 6) or 1.0
        features.freestand = (layer6 < 0.75) and 1 or 0
    else
        features.freestand = 0
    end

    features.moving = playerState.moving and 1 or 0
    features.static = (not playerState.moving and not playerState.airborne) and 1 or 0
    features.crouching = playerState.crouching and 1 or 0

    local weightPrediction = 0.5
    if HasOption(UiElements.advanced, "Adaptive Learning") then
        weightPrediction = 0.4 + math.sin(GlobalsCurTime()) * 0.2
    end

    local finalSide = 0
    local finalConfidence = 0.5

    if features.freestand > 0.7 then
        local fsSide, _ = Resolver.calculateFreestanding(playerIndex)
        finalSide = fsSide
        finalConfidence = features.freestand
    elseif features.lby > 0.6 then
        local lbyAngle, _ = Resolver.predictLby(playerIndex, animstate)
        finalSide = (AngleDifference(lbyAngle, eyeYaw) > 0) and 1 or -1
        finalConfidence = features.lby
    elseif features.jitter > 0.4 then
        finalSide = (data.resolverData.side == 0) and 1 or -data.resolverData.side
        finalConfidence = features.jitter
    else
        if HasOption(UiElements.advanced, "Bruteforce Cycle") then
            finalSide = (data.resolverData.side == 0) and 1 or -data.resolverData.side
            finalConfidence = 0.3
        else
            finalSide = data.resolverData.side
            finalConfidence = 0.5
        end
    end

    finalConfidence = finalConfidence * weightPrediction
    local aggressiveness = 0.8
    local confidenceThreshold = 0.4
    if finalConfidence < confidenceThreshold then
        aggressiveness = aggressiveness * (finalConfidence / confidenceThreshold)
    end

    local resolvedAngle = eyeYaw + (maxDesync * finalSide * aggressiveness)
    resolvedAngle = NormalizeAngle(resolvedAngle)
    local yawDifference = AngleDifference(resolvedAngle, eyeYaw)
    yawDifference = Clamp(yawDifference, -maxDesync, maxDesync)

    PlistSet(playerId, "Force body yaw", true)
    PlistSet(playerId, "Force body yaw value", yawDifference)

    data.resolverData.side = finalSide
    data.resolverData.confidence = finalConfidence
    data.resolverData.lastResolved = GlobalsTickCount()
end

function Resolver.processAll()
    local currentTick = GlobalsTickCount()
    if currentTick - Resolver.lastUpdate < Resolver.updateInterval then
        return
    end
    local localPlayer = EntityGetLocalPlayer()
    if not localPlayer or not EntityIsAlive(localPlayer) then
        return
    end
    local enemies = EntityGetPlayers(true)
    if not enemies then
        return
    end
    for _, enemy in ipairs(enemies) do
        if EntityIsAlive(enemy) and EntityIsEnemy(enemy) then
            Resolver.resolve(enemy)
        end
    end
    Resolver.lastUpdate = currentTick
end

local function PlayerWillPeek()
    local enemies = entity.get_players(true)
    if not enemies then
        return false
    end
    
    local localPlayer = entity.get_local_player()
    if not localPlayer then
        return false
    end
    
    local eyePosition = CreateVector3(client.eye_position())
    local localVelocity = CreateVector3(entity.get_prop(localPlayer, "m_vecVelocity"))
    local predictionTime = TicksToTime(16)
    
    local predictedEyePosition = CreateVector3(
        eyePosition.x + localVelocity.x * predictionTime,
        eyePosition.y + localVelocity.y * predictionTime,
        eyePosition.z + localVelocity.z * predictionTime
    )
    
    for i = 1, #enemies do
        local enemy = enemies[i]
        local enemyVelocity = CreateVector3(entity.get_prop(enemy, "m_vecVelocity"))
        
        local originalOrigin = CreateVector3(entity.get_prop(enemy, "m_vecOrigin"))
        local predictedOrigin = CreateVector3(
            originalOrigin.x + enemyVelocity.x * predictionTime,
            originalOrigin.y + enemyVelocity.y * predictionTime,
            originalOrigin.z + enemyVelocity.z * predictionTime
        )
        
        entity.set_prop(enemy, "m_vecOrigin", predictedOrigin.x, predictedOrigin.y, predictedOrigin.z)
        
        local headPosition = CreateVector3(entity.hitbox_position(enemy, 0))
        local predictedHeadPosition = CreateVector3(
            headPosition.x + enemyVelocity.x * predictionTime,
            headPosition.y + enemyVelocity.y * predictionTime,
            headPosition.z + enemyVelocity.z * predictionTime
        )
        
        local _, damage = client.trace_bullet(
            localPlayer,
            predictedEyePosition.x, predictedEyePosition.y, predictedEyePosition.z,
            predictedHeadPosition.x, predictedHeadPosition.y, predictedHeadPosition.z
        )
        
        entity.set_prop(enemy, "m_vecOrigin", originalOrigin.x, originalOrigin.y, originalOrigin.z)
        
        if damage > 0 then
            return true
        end
    end
    
    return false
end

local function RunRecharge()
    local localPlayer = entity.get_local_player()
    
    if not entity.is_alive(localPlayer) then
        return
    end
    
    local weapon = entity.get_player_weapon(localPlayer)
    if not weapon then
        return
    end
    
    ScriptLeakStop = Weapons(weapon).is_revolver and 17 or 14
    
    if ui.get(RbfxRefs.dt[2]) or ui.get(RbfxRefs.hideShots[2]) then
        if GlobalsTickCount() >= RechargeTimer + ScriptLeakStop then
            ui.set(RbfxRefs.aimbot, true)
        else
            ui.set(RbfxRefs.aimbot, false)
        end
    else
        RechargeTimer = GlobalsTickCount()
        ui.set(RbfxRefs.aimbot, true)
    end
end

local load_state = {
    done = false,
    alpha = 0,
    start_time = globals.curtime()
}
local resolver_text_state = {
    active = true,
    alpha = 0,
    start_time = nil,
    shimmer_offset = 0,
    lift_progress = 0
}
local function lerp(a, b, t)
    t = t < 0 and 0 or (t > 1 and 1 or t)
    return a + (b - a) * t
end
local function ease_out_cubic(t)
    return 1 - (1 - t)^3
end
local function intro()
        if not load_state.done then
            local elapsed = globals.curtime() - load_state.start_time
            if elapsed < 1 then
                load_state.alpha = math.min(1, elapsed * 2)
            elseif elapsed < 2 then
                load_state.alpha = 1
            else
                load_state.alpha = math.max(0, 1 - (elapsed - 2) * 2)
                if elapsed > 2.5 then
                    load_state.done = true
                    resolver_text_state.active = true
                    resolver_text_state.start_time = globals.curtime()
                    resolver_text_state.lift_progress = 0
                    return
                end
            end
            if load_state.alpha > 0 then
                local w, h = client.screen_size()
                renderer.rectangle(0, 0, w, h, 0, 0, 0, load_state.alpha * 180)
                local center_x, center_y = w / 2, h / 2
                local radius = 17
                local thickness = 4
                local accentoik = Pui.reference('misc', 'settings', 'menu color').value
                local r, g, b = unpack(accentoik)
                local rotation = (globals.curtime() * 180) % 360
                renderer.circle_outline(
                    center_x, center_y,
                    r, g, b, load_state.alpha * 255,
                    radius, rotation, 0.75, thickness
                )
                local texts = "assembly resolver"
                local text_w, text_h = renderer.measure_text(nil, texts)
                renderer.text(w / 2 - text_w / 2, center_y + radius + 15, 255, 255, 255, load_state.alpha * 255, "b", 0, texts)
            end
        end
        if load_state.done then
            resolver_text_state.active = true
            if resolver_text_state.start_time == nil then
                resolver_text_state.start_time = globals.curtime()
            end
        else
            resolver_text_state.active = false
        end
        if resolver_text_state.active then
            local elapsed = globals.curtime() - resolver_text_state.start_time
            if elapsed < 1.5 then
                resolver_text_state.alpha = math.min(1, elapsed / 1.5)
            else
                resolver_text_state.alpha = 1
            end
            local lift_duration = 1
            resolver_text_state.lift_progress = math.min(1, elapsed / lift_duration)
            local lift_factor = ease_out_cubic(resolver_text_state.lift_progress)
            local lift_offset = (1 - lift_factor) * 30
            if resolver_text_state.alpha > 0 then
                local w, h = client.screen_size()
                local prefix = "ASSEMBLY"
                local arrow = "   "
                local suffix = AssemblyUserData.role:upper()
                local font = "-"
                local base_y = h - 40
                local y = base_y + lift_offset
                local prefix_w = renderer.measure_text(font, prefix)
                local arrow_w = renderer.measure_text(font, arrow)
                local suffix_w = renderer.measure_text(font, suffix)
                local total_width = prefix_w + arrow_w + suffix_w
                local x_start = w / 2 - total_width / 2
                local accentoik = Pui.reference('misc', 'settings', 'menu color').value
                local ar, ag, ab = unpack(accentoik)
                local br, bg, bb = 255, 255, 255
                local gray = {134, 134, 134}
                local speed_px_per_sec = 110
                local cycle_padding = 45
                local glow_width = 120
                local cycle_length = total_width + glow_width + cycle_padding
                resolver_text_state.shimmer_offset = (resolver_text_state.shimmer_offset + speed_px_per_sec * globals.frametime()) % cycle_length
                local shimmer_center = x_start - glow_width / 2 + resolver_text_state.shimmer_offset
                local x = x_start
                for i = 1, #prefix do
                    local char = prefix:sub(i, i)
                    local cw = renderer.measure_text(font, char)
                    local char_center = x + cw * 0.5
                    local dist = math.abs(char_center - shimmer_center)
                    local t = 1 - math.min(1, dist / (glow_width * 0.5))
                    local r = lerp(br, ar, t)
                    local g = lerp(bg, ag, t)
                    local b = lerp(bb, ab, t)
                    local a = resolver_text_state.alpha * 255
                    renderer.text(x, y, r, g, b, a, font, 0, char)
                    x = x + cw
                end
                renderer.text(x, y, gray[1], gray[2], gray[3], resolver_text_state.alpha * 255, font, 0, arrow)
                x = x + arrow_w
                for i = 1, #suffix do
                    local char = suffix:sub(i, i)
                    local cw = renderer.measure_text(font, char)
                    local char_center = x + cw * 0.5
                    local dist = math.abs(char_center - shimmer_center)
                    local t = 1 - math.min(1, dist / (glow_width * 0.5))
                    local r = lerp(br, ar, t)
                    local g = lerp(bg, ag, t)
                    local b = lerp(bb, ab, t)
                    local a = resolver_text_state.alpha * 255
                    renderer.text(x, y, r, g, b, a, font, 0, char)
                    x = x + cw
                end
            end
        end
end

local function FixRagebot()
    print('ragebiotFIXXXXXXXF @oadfihkojfhdkjhdfjl @asseemblygs @assemblygs')
    local buffer = Ffi.new("char[?]", 0x1D)
    local originalBytes = Ffi.new("char[?]", 0x1D)
    local memoryPtr = Ffi.cast("char*", 0x433AC04B)
    
    Ffi.copy(originalBytes, memoryPtr, 0x1D)
    Ffi.copy(buffer, originalBytes, 0x1D)
    Ffi.fill(buffer, 0x18, 0x90)
    buffer[0x18] = 0xE9
    
    local isApplied = false
    
    ClientSetEventCallback("setup_command", function(cmd)
        local shouldApply = UiGet(UiElements.enabled)
        
        if shouldApply and not isApplied then
            Ffi.copy(memoryPtr, buffer, 0x1D)
            isApplied = true
        elseif not shouldApply and isApplied then
            Ffi.copy(memoryPtr, originalBytes, 0x1D)
            isApplied = false
        end
        
        if shouldApply then
            local dtEnabled = ui.get(RbfxRefs.dt[1]) and ui.get(RbfxRefs.dt[2])
            if dtEnabled then
                cmd.force_defensive = PlayerWillPeek()
            end
        end
        
        if shouldApply then
            RunRecharge()
        else
            ui.set(RbfxRefs.aimbot, true)
        end
    end)
    
    ClientSetEventCallback("run_command", function()
        if not UiGet(UiElements.enabled) then
            return
        end
        
        if CorrectionCache == nil then
            CorrectionCache = ui.get(RbfxRefs.correction)
        end
        
        local localPlayer = entity.get_local_player()
        if localPlayer == nil or entity.get_prop(localPlayer, "m_lifeState") ~= 0 then
            return
        end
        
        local weapon = entity.get_player_weapon(localPlayer)
        local weaponName = entity.get_classname(weapon)
        
        if weaponName ~= "CWeaponTaser" then
            if CorrectionCache ~= nil then
                ui.set(RbfxRefs.correction, true)
                CorrectionCache = nil
            end
        end
    end)
    
    ClientSetEventCallback("level_init", function()
        RechargeTimer = GlobalsTickCount()
    end)
end

UiSetCallback(UiElements.rageFix, FixRagebot)

local function ChangeIcon()
    local tabs = {"RAGE", "AA", "LEGIT", "VISUALS", "MISC", "SKINS", "PLIST", "Tab"}
    local tabsptr = Ffi.cast("intptr_t*", 0x434799AC + 0x54)
    local tabsinfo = {}
    
    for i = 0, #tabs do
        local tab = Ffi.cast("int*", tabsptr[0])[i]
        tabsinfo[i] = { id = Ffi.cast("int*", tab + 0x80), offset = Ffi.cast("int*", tab + 0x84), width = Ffi.cast("int*", tab + 0x8C), height = Ffi.cast("int*", tab + 0x90)}
    end
    
    local icon_url = "https://cdn.discordapp.com/attachments/1355104845492654080/1451873772062642217/logo_4.png?ex=6947c251&is=694670d1&hm=c60979880b0a856291ab7677fc1d9b1ed2615bcb9d4ac91c5e0dfc86e330508e"
    
    Http.get(icon_url, function(status, response)
        if status and response.body then
            local texture_id = renderer.load_png(response.body, 48, 48)
            if texture_id and texture_id > 0 then
                for i = 0, #tabs do
                    if tabs[i + 1] == "PLIST" then
                        tabsinfo[i].id[0] = texture_id
                        break
                    end
                end
            end
        end
    end)
end

ClientSetEventCallback("paint", function()
    UiSetEnabled(UiElements.hitRate, false)
    UiSetEnabled(UiElements.clanTag, false)
    UiSetEnabled(UiElements.hitMarker, false) 
    UiSetEnabled(UiElements.kirkMode, false) 
end)

ClientSetEventCallback("aim_hit", function(e)
    if not UiGet(UiElements.enabled) then return end
    local target = e.target
    if not target then return end
    local backtrack = GetBacktrackTicks(target)
    local playerData = Resolver.players[target]
    local confidence = playerData and playerData.resolverData.confidence or 0.5
    LogSystem.addHit(target, e.damage, e.hitgroup, confidence, backtrack)
end)

ClientSetEventCallback("aim_miss", function(e)
    if not UiGet(UiElements.enabled) then return end
    local target = e.target
    if not target then return end
    local backtrack = GetBacktrackTicks(target)
    local playerData = Resolver.players[target]
    local confidence = playerData and playerData.resolverData.confidence or 0.5
    LogSystem.addMiss(target, e.reason, confidence, backtrack)
end)

ClientSetEventCallback("player_death", function(e)
    if not UiGet(UiElements.enabled) then return end
    local victim = ClientUserIdToEntIndex(e.userid)
    local attacker = ClientUserIdToEntIndex(e.attacker)
    local localPlayer = EntityGetLocalPlayer()
    if attacker == localPlayer and victim and EntityIsEnemy(victim) then
        KillSay.send()
    end
end)

ClientSetEventCallback("round_start", function()
    Resolver.players = {}
    DefensiveData = {}
end)

ClientSetEventCallback("net_update_end", function()
    Resolver.processAll()
end)

ClientSetEventCallback("createmove", function()
    if not UiGet(UiElements.enabled) then return end
    for i = 1, entity.get_players_count() do
        local ent = entity.get_ptr(i)
        if ent ~= 0 and not entity.is_local_player(i) and entity.is_alive(i) then
            local flags = mem.read(ent + Net.flags, "int")
            if bit.band(flags, FL_ONGROUND) == 0 then
                SyncAnim(ent)
            end
        end
    end
end)

ClientSetEventCallback("shutdown", function()
    for _, element in pairs(GameSensePList.adjustments) do
        ui.set_visible(element, true)
        ui.set_enabled(element, true)
    end
end)

local event = "paint" or "setup_command" or "net_update_start" or "paint_ui"
ClientSetEventCallback(event, function ()
    ChangeIcon()
    intro()
end)

ClientDelayCall(0.001, ChangeIcon)
ClientDelayCall(0.001, intro)

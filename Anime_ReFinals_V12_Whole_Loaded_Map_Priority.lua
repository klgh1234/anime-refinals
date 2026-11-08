-- Anime Re:Finals | V12 WHOLE LOADED MAP SCAN + STRICT PRIORITY | Potassium / Luau
-- Strict enemy-only local scan + death-aware teleport rotation + optional Tool attack.
-- No spoofed server remotes, no Windows mouse clicking, no auto dungeon.
-- Strict scan: no HP-only targeting, followers/players are excluded. Unverified targets are not attacked.
-- F5: selected/all | F6: farm | F7: rescan here | F8: close
-- New: instant same-path next + configurable rapid rotation when the game's HP death signal lags.
-- IMPORTANT: rapid rotation is a timing fallback, not proof of a kill. Slow hits may be skipped.
-- V8: priority order for ALL LOCAL MOBS, editable in GUI. Rank 1 group, then 2, then
-- 3 ...; unselected types are excluded, and priority 1 preempts lower ranks on respawn.
-- Ranking is by NAME + DIFFICULTY (e.g. Vega [Medium]) in the current map.
-- V10: strict chosen-only queue, priority-preempt and respawn discovery.
-- V11: fix Unknown difficulty on enemy nametags; parse combined/rich text and GUI BillboardGui Adornee.
-- V9 hide/show hotkey and V7 rapid teleport rotation are preserved.
-- V12: scans ALL currently replicated Workspace models (not just 325 studs),
-- tracks newly replicated Model instances, and does not reset queue on distance.
-- Roblox StreamingEnabled may leave distant mobs UNLOADED on the client.
-- Client scripts cannot see those instances until Roblox streams them in.
-- Default: F4. Click GUI hotkey control to rebind; ESC cancels; F5-F8 reserved.
-- Hiding UI does not change Roblox Lighting/BlurEffect, which V8 never created.

local Players = game:GetService("Players")
local UIS = game:GetService("UserInputService")
local CollectionService = game:GetService("CollectionService")
local LP = Players.LocalPlayer
if not LP then return end
local PG = LP:WaitForChild("PlayerGui")
local function streamingEnabled()
    local ok,value=pcall(function() return workspace.StreamingEnabled end)
    return ok and value==true
end

local WORLD_SCAN_YIELD_EVERY = 300 -- yield while scanning a large map
local WORLD_REGISTRY_PRUNE_EVERY = 45 -- clean references to despawned models
local TICK = 0.03   -- 33 lightweight target checks/s, no full map scans in the loop
local TOOL_COOLDOWN = 0.5
local RESCAN_WHEN_EMPTY = 4 -- only when cached area targets are exhausted
local DEAD_SPAWN_COOLDOWN = 1.35 -- do not retarget a freshly killed spawn
local IDLE_TARGET_RETRY = 0.14 -- if nothing is alive, retry the cached list lightly
local HIT_DISTANCE = 5.5
-- If the game keeps the visual enemy model for ~2 s after its HP is gone,
-- optional FAST NEXT can move when a CONFIRMED enemy's displayed HP is <= 1%.
-- Caveat: this can leave a mob barely alive. Toggle OFF to require actual death.
local FAST_NEXT_HP_PERCENT = 1.0
-- Fallback for enemies killed in one hit while replicated HP/death arrives ~2s late.
-- Values shown in the UI, click to cycle. 0=disabled (strict death signals only).
local RAPID_DELAYS = {0.45, 0.25, 0.65, 1.00, 0}
local RAPID_CHECK_INTERVAL = 0.14
local RAPID_SPAWN_SKIP = 1.20

local sharedEnv = _G
if type(getgenv) == "function" then
    local ok, env = pcall(getgenv)
    if ok and type(env) == "table" then sharedEnv = env end
end
local previous = sharedEnv.__RE_FINALS_LOCAL_FARM_BETA
if type(previous) == "table" and type(previous.stop) == "function" then
    pcall(previous.stop)
end
local state = {
    alive = true, farming = false, modeAll = false, selected = nil,
    center = nil, targets = {}, visited = {}, active = nil,
    kills = 0, passed = 0, lastScan = 0, lastAttack = 0,
    nextPosCheck = 0, scanning = false, attackNote = "Tool only",
    evidenceCache = setmetatable({}, {__mode = "k"}),
    lastMessageTime = 0, lastTarget = nil,
    transitioning = false, pendingRescan = 0, minimized = false,
    spawnCooldown = {}, originalSpawns = setmetatable({}, {__mode = "k"}),
    acquireAfter = 0, rotationIndex = 0, waitingSince = 0,
    quickRescanPending = false,
    fastNearDeath = true,
    rapidIndex = 1, -- default 0.45 seconds, click once for 0.25s
    rapidSwitches = 0,
    lastSwitchReason = "No death signal yet",
    priorityOrder = {}, priorityRanks = {}, priorityOpen = false,
    guiHidden = false, waitingForHotkey = false, hideKeyName = "F4",
    nextPriorityCheck = 0, nextPriorityDiscovery = 0,
    worldModels = {}, worldModelSet = setmetatable({}, {__mode = "k"}),
    worldByName = {},
    worldIndexReady = false, nextWorldPrune = 0,
}
-- Keep the chosen shortcut on re-injection within this Roblox/executor session.
local function lookupHotkey(name)
    if type(name) ~= "string" then return nil end
    local ok, key = pcall(function() return Enum.KeyCode[name] end)
    if ok and key and key ~= Enum.KeyCode.Unknown then return key end
    return nil
end
local storedKey = lookupHotkey(sharedEnv.__RE_FINALS_V9_HIDE_KEY)
if storedKey and storedKey ~= Enum.KeyCode.F5 and storedKey ~= Enum.KeyCode.F6
    and storedKey ~= Enum.KeyCode.F7 and storedKey ~= Enum.KeyCode.F8
    and storedKey ~= Enum.KeyCode.Escape then
    state.hideKeyName = storedKey.Name
end
sharedEnv.__RE_FINALS_LOCAL_FARM_BETA = state
local connections = {}

local function addConnection(c)
    connections[#connections+1] = c
    return c
end
-- Keep a lightweight index of Models in the CLIENT'S loaded Workspace.
-- Unlike GetPartBoundsInRadius, this also considers distant, loaded NPCs.
-- The listener catches newly replicated/respawned models between F7 scans.
local function registerWorldModel(model)
    if not model or not model:IsA("Model") or state.worldModelSet[model] then return end
    state.worldModelSet[model]=true
    state.worldModels[#state.worldModels+1]=model
    local bucket=state.worldByName[model.Name]
    if not bucket then
        bucket={}
        state.worldByName[model.Name]=bucket
    end
    bucket[#bucket+1]=model
end
addConnection(workspace.DescendantAdded:Connect(function(obj)
    if not state.alive then return end
    if obj:IsA("Model") then
        registerWorldModel(obj)
        if state.modeAll and state.farming then state.nextPriorityDiscovery=0 end
    end
end))
local function rebuildWorldIndex()
    state.worldModels={}
    state.worldModelSet=setmetatable({}, {__mode="k"})
    state.worldByName={}
    local descendants=workspace:GetDescendants() -- one explicit, chunked enumeration
    for i,obj in ipairs(descendants) do
        if not state.alive then return false end
        if obj:IsA("Model") then registerWorldModel(obj) end
        if i%WORLD_SCAN_YIELD_EVERY==0 then task.wait() end
    end
    state.worldIndexReady=true
    state.nextWorldPrune=os.clock()+WORLD_REGISTRY_PRUNE_EVERY
    print("[RE:FINALS V12] Loaded Workspace models indexed:",#state.worldModels,
        "StreamingEnabled:",streamingEnabled())
    return true
end
local function pruneWorldIndex()
    local fresh={}
    local unique=setmetatable({}, {__mode="k"})
    for _,model in ipairs(state.worldModels) do
        if model.Parent and model:IsDescendantOf(workspace) and not unique[model] then
            unique[model]=true
            fresh[#fresh+1]=model
        end
    end
    local byName={}
    for _,model in ipairs(fresh) do
        local bucket=byName[model.Name]
        if not bucket then bucket={};byName[model.Name]=bucket end
        bucket[#bucket+1]=model
    end
    state.worldModels=fresh
    state.worldModelSet=unique
    state.worldByName=byName
    state.nextWorldPrune=os.clock()+WORLD_REGISTRY_PRUNE_EVERY
end
-- Fast structural pre-filter only; the full STRICT enemy filter still decides.
-- A model with Humanoid/HP/root or an explicit enemy tag is a possible NPC.
local possibleEnemyParents={
    enemies=true,enemymobs=true,mobs=true,monsters=true,
    enemyunits=true,hostile=true,monstersfolder=true,
}
local function plausibleWorldMob(model)
    return model.Parent and model:IsDescendantOf(workspace) and (
        model:FindFirstChildOfClass("Humanoid") ~= nil
        or model:FindFirstChild("HumanoidRootPart") ~= nil
        or model:FindFirstChild("Head") ~= nil
        or model:FindFirstChild("Torso") ~= nil
        or model:GetAttribute("HealthReal") ~= nil
        or model:GetAttribute("IsEnemy") == true
        or model:GetAttribute("IsMonster") == true
        or model:GetAttribute("IsMob") == true
        or model:FindFirstChild("Health") ~= nil
        or model:FindFirstChild("HP") ~= nil
        or (model.Parent and possibleEnemyParents[model.Parent.Name:lower()])
        or CollectionService:HasTag(model,"Enemy")
        or CollectionService:HasTag(model,"Monster")
        or CollectionService:HasTag(model,"Mob"))
end

local function rootOf(model)
    if not model then return nil end
    return model:FindFirstChild("HumanoidRootPart")
        or model.PrimaryPart
        or model:FindFirstChild("UpperTorso")
        or model:FindFirstChild("Torso")
        or model:FindFirstChild("Head")
        or model:FindFirstChildWhichIsA("BasePart", true)
end
local function playerRoot()
    local char = LP.Character
    return char and char:FindFirstChild("HumanoidRootPart"), char
end

-- Fail-closed enemy filter. A Humanoid/HP value on its own is NOT evidence
-- that a Model is hostile: your own fighters and followers have those too.
local blockedFragments = {
    "activeshadow", "shadow", "pet", "companion", "follower", "summon",
    "clone", "shopkeeper", "shopnpc", "merchant", "vendor", "trainer",
    "questgiver", "questnpc", "teleportnpc", "dummy", "practice",
    "civilian", "supportunit", "ally", "friendly", "playerunit"
}
local allyContainers = {
    pets=true, playerpets=true, playerunits=true, ownedunits=true,
    followers=true, companions=true, activeshadows=true, summons=true,
    allies=true, friendlies=true, equippedpets=true, equippedunits=true,
}
local mobContainers = {
    enemies=true, enemymobs=true, mobs=true, monsters=true,
    monstersfolder=true, hostile=true, enemyunits=true,
}
local difficulties = {
    ["very easy"]=true, ["easy"]=true, ["medium"]=true,
    ["hard"]=true, ["very hard"]=true, ["extreme"]=true,
    ["insane"]=true, ["impossible"]=true,
}
local function numericAttribute(model, keys)
    for _, name in ipairs(keys) do
        local v = model:GetAttribute(name)
        if type(v)=="number" then return v, name end
    end
    return nil
end
local function blocked(model)
    local low=model.Name:lower()
    for _,part in ipairs(blockedFragments) do
        if low:find(part,1,true) then return true end
    end
    if model:GetAttribute("IsPet") == true
        or model:GetAttribute("IsCompanion") == true
        or model:GetAttribute("IsAlly") == true
        or model:GetAttribute("Friendly") == true
        or model:GetAttribute("IsEnemy") == false then return true end
    for _,key in ipairs({"Owner", "OwnerId", "OwnerUserId", "PetOwner", "Summoner", "SummonerUserId", "PlayerOwner"}) do
        if model:GetAttribute(key) ~= nil then return true end
        if model:FindFirstChild(key) then return true end
    end
    local cur = model
    while cur and cur ~= workspace do
        if cur:IsA("Model") and Players:GetPlayerFromCharacter(cur) then return true end
        if allyContainers[cur.Name:lower()] then return true end
        cur = cur.Parent
    end
    return model == LP.Character
end

local function parseNumber(str)
    if type(str) ~= "string" then return nil end
    local number, suffix = str:upper():gsub(",", ""):match("^%s*(%d+%.?%d*)%s*([KMBTQ]?)%s*$")
    if not number then return nil end
    local mult = {K=1e3,M=1e6,B=1e9,T=1e12,Q=1e15}
    return tonumber(number) * (mult[suffix] or 1)
end
local function parseHealthText(text)
    if type(text) ~= "string" then return nil end
    local a,b=text:upper():match("([%d%.,]+%s*[KMBTQ]?)%s*/%s*([%d%.,]+%s*[KMBTQ]?)")
    if not a then return nil end
    local current, maximum = parseNumber(a), parseNumber(b)
    if current and maximum and maximum>0 then return current,maximum end
end

-- V11 difficulty reader: the nameplate may be a combined RichText label,
-- a BillboardGui under PlayerGui whose Adornee targets the enemy, or a
-- difficulty attribute/StringValue. Do not infer difficulty from damage/HP.
local tierTable = {
    {"very easy", "Very Easy"},
    {"very hard", "Very Hard"},
    {"extreme", "Extreme"},
    {"impossible", "Impossible"},
    {"insane", "Insane"},
    {"medium", "Medium"},
    {"easy", "Easy"},
    {"hard", "Hard"},
}
local difficultyFields = {
    "Difficulty", "DifficultyName", "EnemyDifficulty", "MobDifficulty",
    "DifficultyLevel", "Tier", "Rank", "EnemyRank", "LevelName",
}
local function extractTier(raw)
    if type(raw) ~= "string" or raw == "" then return nil end
    -- RichText and newline nameplates: '<font>Very Hard</font>\nTomiojo'
    local clean = raw:gsub("<[^>]*>", " "):gsub("&nbsp;", " ")
        :gsub("[%c]", " "):gsub("[%p]", " "):lower():gsub("%s+", " ")
    for _,info in ipairs(tierTable) do
        -- Match complete word(s); avoid matching 'Hard' inside 'Very Hard'.
        local pattern = "%f[%a]"..info[1]:gsub(" ", "%%s+").."%f[%A]"
        if clean:find(pattern) then return info[2] end
    end
    return nil
end
local function isGuiText(obj)
    return obj:IsA("TextLabel") or obj:IsA("TextButton") or obj:IsA("TextBox")
end
local function tierFromAttributes(inst)
    if not inst then return nil end
    for _,key in ipairs(difficultyFields) do
        local value = inst:GetAttribute(key)
        if type(value) == "string" then
            local found=extractTier(value)
            if found then return found end
        end
        local v=inst:FindFirstChild(key)
        if v and v:IsA("StringValue") then
            local found=extractTier(v.Value)
            if found then return found end
        end
    end
    return nil
end
local function tierInside(root)
    if not root then return nil end
    if isGuiText(root) then
        local found=extractTier(root.Text)
        if found then return found end
    end
    for _,desc in ipairs(root:GetDescendants()) do
        if isGuiText(desc) then
            local found=extractTier(desc.Text)
            if found then return found end
        elseif desc:IsA("StringValue") then
            local name=desc.Name:lower()
            if name:find("difficulty",1,true) or name=="tier" or name=="enemyrank" then
                local found=extractTier(desc.Value)
                if found then return found end
            end
        end
    end
    return nil
end
-- External GUI lookup is built only when the player scans, never every frame.
local function rebuildTierGuiIndex(includeWorkspace)
    state.adornedTiers = setmetatable({}, {__mode = "k"})
    state.screenTierLabels = {}
    state.screenNameLabels = {}
    local index=state.adornedTiers
    local count=0
    local function collect(container, collect2D)
        local nodes=container:GetDescendants()
        for i, obj in ipairs(nodes) do
            if obj:IsA("BillboardGui") then
                local target=obj.Adornee
                if target then
                    local tier=tierInside(obj)
                    if tier then
                        local cur=target
                        while cur and cur~=workspace and cur~=game do
                            if cur:IsA("Model") and not index[cur] then index[cur]=tier end
                            cur=cur.Parent
                        end
                        count=count+1
                    end
                end
            elseif collect2D and isGuiText(obj) then
                -- Sometimes names/levels are overlaid by a ScreenGui, not BillboardGui.
                -- A name-label AND nearby difficulty-label are required for fallback.
                local ownGUI=PG:FindFirstChild("ReFinalsLocalFarmBeta")
                if not (ownGUI and obj:IsDescendantOf(ownGUI))
                    and not obj:FindFirstAncestorWhichIsA("BillboardGui") then
                    local tier=extractTier(obj.Text)
                    if tier then
                        state.screenTierLabels[#state.screenTierLabels+1]={obj=obj,tier=tier}
                    else
                        state.screenNameLabels[#state.screenNameLabels+1]=obj
                    end
                end
            end
            if includeWorkspace and i%2400==0 then task.wait() end
        end
    end
    collect(PG,true)
    -- Workspace may hold nameplate BillboardGui outside the monster Model.
    -- Check at most on an explicit F7 scan; not on the 33Hz farm loop.
    if includeWorkspace then collect(workspace,false) end
    print("[RE:FINALS V11] Level GUI index:",count,
        "adorned labels;",#state.screenTierLabels,"screen tier labels")
end
local function nearScreenTier(model)
    if not state.screenTierLabels or #state.screenTierLabels==0 then return nil end
    local camera=workspace.CurrentCamera
    local root=rootOf(model)
    if not camera or not root then return nil end
    local head=model:FindFirstChild("Head")
    local world=(head and head:IsA("BasePart") and head.Position or root.Position)
        + Vector3.new(0, 2.5, 0)
    local projection,visible=camera:WorldToViewportPoint(world)
    if not visible then return nil end
    local targetPos=Vector2.new(projection.X,projection.Y)
    local modelName=model.Name:lower()
    -- Some ScreenGui systems combine difficulty and enemy name in ONE label.
    -- Match both that exact name and an on-screen position near this model.
    for _,entry in ipairs(state.screenTierLabels) do
        local label=entry.obj
        if label.Parent and label.Visible then
            local text=label.Text:lower():gsub("<[^>]*>"," ")
            local nameFound=text:find(modelName,1,true)
            if nameFound then
                local pos=label.AbsolutePosition+label.AbsoluteSize/2
                if (pos-targetPos).Magnitude<160 then return entry.tier end
            end
        end
    end
    local nearestNameDist=1e8
    local nearestNamePos=nil
    for _,nameLabel in ipairs(state.screenNameLabels or {}) do
        if nameLabel.Parent and nameLabel.Visible then
            local text=nameLabel.Text:lower():gsub("<[^>]*>", " "):gsub("^%s+", ""):gsub("%s+$", "")
            if text==modelName then
                local p=nameLabel.AbsolutePosition+nameLabel.AbsoluteSize/2
                local distance=(p-targetPos).Magnitude
                if distance < nearestNameDist then
                    nearestNameDist=distance
                    nearestNamePos=p
                end
            end
        end
    end
    if not nearestNamePos or nearestNameDist>175 then return nil end
    local bestDist=1e8
    local best=nil
    for _,entry in ipairs(state.screenTierLabels) do
        local label=entry.obj
        if label.Parent and label.Visible then
            local p=label.AbsolutePosition+label.AbsoluteSize/2
            local dist=(p-nearestNamePos).Magnitude
            -- A difficulty should sit near its associated monster name.
            if dist < 90 and dist < bestDist then
                bestDist=dist;best=entry.tier
            end
        end
    end
    return best
end

local function evidenceFor(model)
    local cached=state.evidenceCache[model]
    -- A valid enemy can initially have no loaded nameplate; retry its level.
    if cached and ((cached.valid and cached.tier)
        or os.clock()-(cached.checkedAt or 0)<(cached.valid and 1.5 or 0.45)) then
        return cached.valid, cached.label, cached.reason, cached.tier
    end
    local valid, reason, healthLabel=false, "no enemy tag/difficulty", nil
    local attr = model:GetAttribute("IsEnemy") == true
        or model:GetAttribute("Enemy") == true
        or model:GetAttribute("IsMonster") == true
        or model:GetAttribute("IsMob") == true
    local tagged = CollectionService:HasTag(model,"Enemy")
        or CollectionService:HasTag(model,"Monster")
        or CollectionService:HasTag(model,"Mob")
    local inEnemyFolder=false
    local cur=model.Parent
    while cur and cur~=workspace do
        if mobContainers[cur.Name:lower()] then inEnemyFolder=true break end
        cur=cur.Parent
    end
    local monsterTier=tierFromAttributes(model)
        or tierFromAttributes(model:FindFirstChildOfClass("Humanoid"))
    local difficultyFound=monsterTier~=nil
    local hpBarFound, allyRarityFound=false,false
    -- Supports split labels and combined RichText such as 'Medium\nVega'.
    -- Still scan only this monster's descendants, never all remote UI every tick.
    for _, obj in ipairs(model:GetDescendants()) do
        if isGuiText(obj) then
            local raw=obj.Text
            local tier=extractTier(raw)
            if tier then monsterTier=monsterTier or tier;difficultyFound=true end
            local cleaned=raw:lower():gsub("<[^>]*>", " "):gsub("%s+", " ")
            if cleaned:find("%f[%a]legendary%f[%A]")
                or cleaned:find("%f[%a]unique%f[%A]") then
                allyRarityFound=true
            end
            local n=parseHealthText(raw)
            if n then
                hpBarFound=true
                if not healthLabel then healthLabel=obj end
            end
        elseif obj:IsA("StringValue") then
            local key=obj.Name:lower()
            if key:find("difficulty",1,true) or key=="tier" or key=="enemyrank" then
                local tier=extractTier(obj.Value)
                if tier then monsterTier=monsterTier or tier;difficultyFound=true end
            end
        end
    end
    -- External game nameplates usually live in PlayerGui and adorn the NPC.
    if not monsterTier then
        monsterTier=state.adornedTiers and state.adornedTiers[model]
        if monsterTier then difficultyFound=true end
    end
    -- A 2D nameplate is trusted only after matching the name and screen location.
    if not monsterTier then
        monsterTier=nearScreenTier(model)
        if monsterTier then difficultyFound=true end
    end
    if allyRarityFound and not difficultyFound then
        valid=false; reason="ally rarity label"
    elseif attr or tagged or inEnemyFolder then
        valid=true; reason="enemy tag/folder"
    elseif difficultyFound and hpBarFound then
        valid=true; reason="difficulty + HP bar"
    end
    local evidence={valid=valid,label=healthLabel,reason=reason,tier=monsterTier,checkedAt=os.clock()}
    state.evidenceCache[model]=evidence
    return valid,healthLabel,reason,monsterTier
end

local function enemyInfo(model, center)
    if not model or not model:IsA("Model") or not model:IsDescendantOf(workspace) then return end
    if blocked(model) then return end
    local allowed, label, proof = evidenceFor(model)
    if not allowed then return end -- IMPORTANT: never fall back to any model with HP
    local r=rootOf(model)
    if not r or not r:IsA("BasePart") then return end
    -- V12: No radius/height restriction. Strict hostility checks remain above.
    -- "center" is kept for compatibility with the V11 target/priority functions.
    local humanoid=model:FindFirstChildOfClass("Humanoid")
    local hp, src = numericAttribute(model,{"HealthReal","CurrentHealth","Health","HP"})
    if not hp then
        for _,key in ipairs({"HealthReal","Health","HP","CurrentHealth"}) do
            local v=model:FindFirstChild(key)
            if v and (v:IsA("NumberValue") or v:IsA("IntValue")) then
                hp=v.Value;src="Value:"..key;break
            end
        end
    end
    -- Prefer the enemy's own displayed health over a placeholder Humanoid HP.
    if label and label.Parent then
        local displayHP=parseHealthText(label.Text)
        if displayHP then hp=displayHP;src="HP bar" end
    end
    if hp==nil and humanoid then hp=humanoid.Health;src="Humanoid" end
    if hp==nil then return end
    local alive=hp>0
    if humanoid and humanoid.Health<=0 then alive=false end
    if model:GetAttribute("Dead") == true or model:GetAttribute("IsDead") == true then alive=false end
    return r,hp,alive,src,humanoid,label,proof
end

-- Priority identity is a stable combination of the actual enemy's name and
-- the difficulty shown in its enemy billboard. Never merge different tiers.
local function mobIdentity(model)
    local _,_,_,tier=evidenceFor(model)
    return model.Name.." ["..(tier or "Unknown").."]"
end
local function displaySelected()
    return state.selected or "none"
end

-- GUI -------------------------------------------------------------
local existing = PG:FindFirstChild("ReFinalsLocalFarmBeta")
if existing then existing:Destroy() end
local gui = Instance.new("ScreenGui")
gui.Name = "ReFinalsLocalFarmBeta"
gui.ResetOnSpawn = false
gui.DisplayOrder = 300
gui.Parent = PG
local frame = Instance.new("Frame")
frame.Name = "Panel"
frame.Size = UDim2.fromOffset(368, 554)
frame.Position = UDim2.fromOffset(22, 100)
frame.BackgroundColor3 = Color3.fromRGB(24, 29, 43)
frame.BorderSizePixel = 0
frame.Parent = gui
Instance.new("UICorner",frame).CornerRadius = UDim.new(0,9)
local function makeText(class, title, y, h)
    local obj = Instance.new(class)
    obj.Size = UDim2.new(1,-20,0,h)
    obj.Position = UDim2.fromOffset(10,y)
    obj.BackgroundColor3 = Color3.fromRGB(53, 66, 89)
    obj.BorderSizePixel = 0
    obj.TextColor3 = Color3.fromRGB(246,248,255)
    obj.Font = Enum.Font.GothamBold
    obj.TextSize = 12
    obj.Text = title
    obj.Parent = frame
    if class == "TextButton" then Instance.new("UICorner",obj).CornerRadius = UDim.new(0,6) end
    return obj
end
local header = makeText("TextLabel","RE:FINALS V12 | WORLD SCAN",8,29)
-- Header controls, separated from drag area so mouse click does not drag the panel.
header.Size = UDim2.new(1, -135, 0, 29)
local function topButton(text, rightOffset)
    local btn = Instance.new("TextButton")
    btn.Size = UDim2.fromOffset(29, 28)
    btn.Position = UDim2.new(1, rightOffset, 0, 8)
    btn.Text = text
    btn.Font = Enum.Font.GothamBold
    btn.TextSize = 16
    btn.TextColor3 = Color3.new(1, 1, 1)
    btn.BackgroundColor3 = Color3.fromRGB(75, 86, 114)
    btn.BorderSizePixel = 0
    btn.ZIndex = 5
    btn.Parent = frame
    Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 6)
    return btn
end
local hideBtn = topButton("H", -105) -- hide entire ScreenGui; shortcut can show it
hideBtn.BackgroundColor3=Color3.fromRGB(43,113,106)
local minimizeBtn = topButton("-", -72)
local closeBtn = topButton("X", -39)
closeBtn.BackgroundColor3 = Color3.fromRGB(162, 58, 73)
local scanBtn = makeText("TextButton","SCAN ALL LOADED MOBS (F7)",46,32)
scanBtn.TextSize=11
local modeBtn = makeText("TextButton","MODE: SELECTED MOB (F5)",84,32)
local selection = makeText("TextLabel","SELECTED: none",123,25)
local list = Instance.new("ScrollingFrame")
list.Position = UDim2.fromOffset(10,154)
list.Size = UDim2.new(1,-20,0,104)
list.ScrollBarThickness = 5
list.BackgroundColor3 = Color3.fromRGB(32, 39, 54)
list.BorderSizePixel = 0
list.CanvasSize = UDim2.fromOffset(0,0)
list.Parent = frame
local priorityBtn = makeText("TextButton","FARM QUEUE: NONE | CLICK TO SELECT",265,34)
priorityBtn.BackgroundColor3=Color3.fromRGB(90,65,105)
priorityBtn.TextSize=11
local farmBtn = makeText("TextButton","TELEPORT FARM: OFF (F6)",306,35)
local nextBtn = makeText("TextButton","NEXT MOB (MANUAL)",348,30)
local fastBtn = makeText("TextButton","FAST NEXT AT 1% HP: ON",385,29)
local rapidBtn = makeText("TextButton","RAPID ROTATE: 0.45s (HIT-AND-MOVE)",421,32)
rapidBtn.BackgroundColor3 = Color3.fromRGB(36, 96, 103)
local status = makeText("TextLabel","F7 scan -> choose mobs in FARM QUEUE -> F5 ALL -> F6 farm.",462,35)
status.TextWrapped = true
status.TextSize = 11
local hideKeyBtn = makeText("TextButton","HIDE / SHOW GUI: F4 | CLICK TO CHANGE",503,27)
hideKeyBtn.BackgroundColor3=Color3.fromRGB(47,99,104)
hideKeyBtn.TextSize=11
local foot = makeText("TextLabel","F4 hide/show UI | H hide now | F5 mode F6 farm F7 scan F8 close",533,14)
foot.BackgroundTransparency = 1
foot.TextSize = 10
-- Priority editor overlays the farm controls; minimized UI still shows -/+ and X.
local expandedControls = {scanBtn,modeBtn,selection,list,priorityBtn,farmBtn,nextBtn,fastBtn,rapidBtn,status,hideKeyBtn,foot}
local priorityPage = Instance.new("Frame")
priorityPage.Name="PriorityEditor"
priorityPage.Size=UDim2.new(1,-20,0,492)
priorityPage.Position=UDim2.fromOffset(10,47)
priorityPage.BackgroundColor3=Color3.fromRGB(30,37,53)
priorityPage.BorderSizePixel=0
priorityPage.Visible=false
priorityPage.Parent=frame
Instance.new("UICorner",priorityPage).CornerRadius=UDim.new(0,8)

local function editorLabel(text, posY, height)
    local label=Instance.new("TextLabel")
    label.Position=UDim2.fromOffset(10,posY)
    label.Size=UDim2.new(1,-20,0,height)
    label.BackgroundTransparency=1
    label.TextColor3=Color3.fromRGB(230,238,252)
    label.Font=Enum.Font.Gotham
    label.TextSize=12
    label.TextXAlignment=Enum.TextXAlignment.Left
    label.TextWrapped=true
    label.Text=text
    label.Parent=priorityPage
    return label
end
local function editorButton(parent, text, x, y, w, h, color)
    local btn=Instance.new("TextButton")
    btn.Position=UDim2.fromOffset(x,y)
    btn.Size=UDim2.fromOffset(w,h)
    btn.BackgroundColor3=color or Color3.fromRGB(63,77,105)
    btn.BorderSizePixel=0
    btn.Font=Enum.Font.GothamBold
    btn.TextSize=12
    btn.TextColor3=Color3.fromRGB(250,252,255)
    btn.Text=text
    btn.Parent=parent
    Instance.new("UICorner",btn).CornerRadius=UDim.new(0,5)
    return btn
end
local editorTitle=editorLabel("CHOOSE MOBS | STRICT FARM ORDER",8,27)
editorTitle.Font=Enum.Font.GothamBold
editorTitle.Size=UDim2.new(1,-133,0,27)
local backBtn=editorButton(priorityPage,"BACK",244,7,91,29,Color3.fromRGB(66,103,127))
editorLabel("ONLY chosen monster types are farmed. #1 is always highest: when it respawns, switch back immediately. Different difficulties count separately.",40,41)
editorLabel("FARM THESE ONLY   (TOP = HIGHEST PRIORITY)",85,25)
local priorityRows=Instance.new("ScrollingFrame")
priorityRows.Name="RankedNames"
priorityRows.Position=UDim2.fromOffset(10,113)
priorityRows.Size=UDim2.new(1,-20,0,164)
priorityRows.BackgroundColor3=Color3.fromRGB(22,28,42)
priorityRows.BorderSizePixel=0
priorityRows.ScrollBarThickness=4
priorityRows.Parent=priorityPage
local priorityLayout=Instance.new("UIListLayout",priorityRows)
priorityLayout.Padding=UDim.new(0,3)
priorityLayout.SortOrder=Enum.SortOrder.LayoutOrder
editorLabel("AVAILABLE MOBS   (CLICK ADD TO FARM)",287,23)
local availableRows=Instance.new("ScrollingFrame")
availableRows.Name="AvailableNames"
availableRows.Position=UDim2.fromOffset(10,315)
availableRows.Size=UDim2.new(1,-20,0,110)
availableRows.BackgroundColor3=Color3.fromRGB(22,28,42)
availableRows.BorderSizePixel=0
availableRows.ScrollBarThickness=4
availableRows.Parent=priorityPage
local availableLayout=Instance.new("UIListLayout",availableRows)
availableLayout.Padding=UDim.new(0,3)
availableLayout.SortOrder=Enum.SortOrder.LayoutOrder
local clearPriorityBtn=editorButton(priorityPage,"CLEAR FARM SELECTION",10,434,327,29,Color3.fromRGB(134,65,81))
local editorInfo=editorLabel("Nothing selected = no automatic ALL-mode targets.",467,19)
editorInfo.TextColor3=Color3.fromRGB(171,196,219)
editorInfo.TextSize=11

local function setPage(openEditor)
    state.priorityOpen=openEditor
    priorityPage.Visible=openEditor and not state.minimized
    for _,control in ipairs(expandedControls) do
        control.Visible=not state.minimized and not openEditor
    end
end
local function toggleMinimize()
    if not state.alive then return end
    state.minimized=not state.minimized
    frame.Size=UDim2.fromOffset(368,state.minimized and 47 or 554)
    minimizeBtn.Text=state.minimized and "+" or "-"
    setPage(state.priorityOpen)
end

-- Hide the whole GUI, not just the panel. This intentionally leaves the GUI
-- instance alive in PlayerGui: the farming task checks gui.Parent, not gui.Enabled.
-- Press the configured key again to bring back the complete UI and its settings.
local function setGuiHidden(hidden)
    if not state.alive or not gui.Parent then return end
    state.guiHidden = hidden == true
    state.waitingForHotkey = false
    gui.Enabled = not state.guiHidden
    if not state.guiHidden then
        hideKeyBtn.Text = "HIDE / SHOW GUI: " .. state.hideKeyName .. " | CLICK TO CHANGE"
    end
    print("[RE:FINALS V11] GUI", state.guiHidden and "HIDDEN" or "SHOWN",
        "farm running:", state.farming, "toggle:", state.hideKeyName)
end
local function updateHideKeyLabel()
    hideKeyBtn.Text = "HIDE / SHOW GUI: " .. state.hideKeyName .. " | CLICK TO CHANGE"
    foot.Text = state.hideKeyName .. " hide/show UI | H hide now | F5 mode F6 farm F7 scan F8 close"
end
updateHideKeyLabel()
addConnection(hideBtn.Activated:Connect(function() setGuiHidden(true) end))
addConnection(hideKeyBtn.Activated:Connect(function()
    if state.guiHidden then return end
    state.waitingForHotkey = true
    hideKeyBtn.Text = "PRESS NEW KEY (ESC = CANCEL)"
end))

local function rebuildPriorityRanks()
    local ranks={}
    for i,name in ipairs(state.priorityOrder) do ranks[name]=i end
    state.priorityRanks=ranks
    -- An editing change takes effect immediately, even while farming.
    state.visited={}
    state.rotationIndex=0
    state.acquireAfter=0
    state.nextPriorityCheck=0
    state.nextPriorityDiscovery=0
    -- The step loop will drop a now-unselected active target on its next tick.
end
local function listCounts()
    local counts={}
    for _,m in ipairs(state.targets) do
        local key=mobIdentity(m)
        counts[key]=(counts[key] or 0)+1
    end
    return counts
end
local function createEditorRow(parent,index,textLabel,color)
    local row=Instance.new("Frame")
    row.Size=UDim2.new(1,-7,0,31)
    row.BackgroundColor3=color or Color3.fromRGB(50,63,87)
    row.BorderSizePixel=0
    row.LayoutOrder=index
    row.Parent=parent
    Instance.new("UICorner",row).CornerRadius=UDim.new(0,5)
    local text=Instance.new("TextLabel")
    text.Size=UDim2.new(1,-108,1,0)
    text.Position=UDim2.fromOffset(8,0)
    text.BackgroundTransparency=1
    text.Text=textLabel
    text.TextColor3=Color3.fromRGB(248,248,255)
    text.TextXAlignment=Enum.TextXAlignment.Left
    text.TextTruncate=Enum.TextTruncate.AtEnd
    text.Font=Enum.Font.Gotham
    text.TextSize=12
    text.Parent=row
    return row
end
local function clearEditorRows(parent)
    for _,child in ipairs(parent:GetChildren()) do
        if child:IsA("Frame") then child:Destroy() end
    end
end
local refreshPriorityUI
refreshPriorityUI=function()
    if not state.alive or not gui.Parent then return end
    clearEditorRows(priorityRows)
    clearEditorRows(availableRows)
    local counts=listCounts()
    local order=state.priorityOrder
    for i,name in ipairs(order) do
        local row=createEditorRow(priorityRows,i,("#%d  %s (%d)"):format(i,name,counts[name] or 0),Color3.fromRGB(69,56,91))
        local up=editorButton(row,"^",0,2,29,27)
        up.Position=UDim2.new(1,-100,0,2)
        local down=editorButton(row,"v",0,2,29,27)
        down.Position=UDim2.new(1,-68,0,2)
        local remove=editorButton(row,"X",0,2,29,27,Color3.fromRGB(126,57,73))
        remove.Position=UDim2.new(1,-36,0,2)
        up.Activated:Connect(function()
            if i>1 then
                order[i-1],order[i]=order[i],order[i-1]
                rebuildPriorityRanks(); refreshPriorityUI()
            end
        end)
        down.Activated:Connect(function()
            if i<#order then
                order[i+1],order[i]=order[i],order[i+1]
                rebuildPriorityRanks(); refreshPriorityUI()
            end
        end)
        remove.Activated:Connect(function()
            table.remove(order,i)
            rebuildPriorityRanks(); refreshPriorityUI()
        end)
    end
    priorityRows.CanvasSize=UDim2.fromOffset(0,math.max(0,#order*34))
    local names={}
    for name in pairs(counts) do
        if not state.priorityRanks[name] then names[#names+1]=name end
    end
    table.sort(names)
    for i,name in ipairs(names) do
        local row=createEditorRow(availableRows,i,("%s (%d)"):format(name,counts[name]))
        local add=editorButton(row,"ADD",0,2,66,27,Color3.fromRGB(40,117,89))
        add.Position=UDim2.new(1,-74,0,2)
        add.Activated:Connect(function()
            if state.priorityRanks[name] then return end
            order[#order+1]=name
            state.modeAll=true
            modeBtn.Text="MODE: PRIORITY ONLY (F5)"
            rebuildPriorityRanks(); refreshPriorityUI()
        end)
    end
    availableRows.CanvasSize=UDim2.fromOffset(0,math.max(0,#names*34))
    if #order==0 then
        priorityBtn.Text="FARM QUEUE: EMPTY | CHOOSE MOBS"
        editorInfo.Text="EMPTY: All-mobs mode will not farm any monster."
    else
        priorityBtn.Text="FARM QUEUE ONLY: "..table.concat(order," > ")
        editorInfo.Text=("%d chosen types only. Respawned #1 preempts lower ranks."):format(#order)
    end
end
addConnection(priorityBtn.Activated:Connect(function()
    refreshPriorityUI()
    setPage(true)
end))
addConnection(backBtn.Activated:Connect(function() setPage(false) end))
addConnection(clearPriorityBtn.Activated:Connect(function()
    state.priorityOrder={}
    rebuildPriorityRanks()
    refreshPriorityUI()
end))

local function info(text)
    if status.Parent then status.Text = text end
end

local function forgetActive()
    if state.active and state.active.listeners then
        for _, conn in ipairs(state.active.listeners) do
            if conn.Connected then conn:Disconnect() end
        end
    end
    state.active = nil
end

local function buildSlots()
    local slots={}
    for _,m in ipairs(state.targets) do
        local key=mobIdentity(m)
        if state.modeAll then
            -- Strict whitelist: if no chosen type, there are no ALL-mode targets.
            if state.priorityRanks[key] then slots[#slots+1]=m end
        elseif state.selected and key==state.selected then
            slots[#slots+1]=m
        end
    end
    return slots
end
local function refreshList()
    for _,child in ipairs(list:GetChildren()) do
        if child:IsA("TextButton") then child:Destroy() end
    end
    local counts = {}
    for _,m in ipairs(state.targets) do
        local key=mobIdentity(m)
        counts[key] = (counts[key] or 0) + 1
    end
    local names = {}
    for name in pairs(counts) do names[#names+1] = name end
    table.sort(names)
    for i,name in ipairs(names) do
        local b = Instance.new("TextButton")
        b.Size = UDim2.new(1,-9,0,27)
        b.Position = UDim2.fromOffset(0,(i-1)*29)
        b.BackgroundColor3 = (state.selected == name) and Color3.fromRGB(101,70,109) or Color3.fromRGB(53,66,89)
        b.Text = ("%s (%d)"):format(name, counts[name])
        b.TextColor3 = Color3.new(1,1,1)
        b.Font = Enum.Font.Gotham
        b.TextSize = 12
        b.Parent = list
        addConnection(b.Activated:Connect(function()
            state.selected = name
            state.modeAll = false
            state.visited = {}
            state.rotationIndex = 0
            state.acquireAfter = 0
            forgetActive()
            selection.Text = "SELECTED: "..name
            modeBtn.Text = "MODE: SELECTED MOB (F5)"
            refreshList()
        end))
    end
    list.CanvasSize = UDim2.fromOffset(0,#names*29)
    selection.Text = "SELECTED: "..(state.selected or "none")
    refreshPriorityUI()
end

local function scanHere(automatic, changedMap)
    -- Moving hundreds of studs is NORMAL for whole-world farming.
    -- Never clear the priority queue merely because the character teleported.
    if state.scanning or not state.alive then return end
    local r = playerRoot()
    if not r then info("Waiting for character...") return end
    state.scanning = true
    info("Scanning ALL loaded Workspace mobs... (no distance cap)")
    local center = r.Position
    state.center = center
    state.targets = {}
    state.visited = {}
    state.rotationIndex = 0
    state.acquireAfter = 0
    forgetActive()
    state.evidenceCache = setmetatable({}, {__mode = "k"})
    state.lastScan = os.clock()
    state.quickRescanPending = false
    -- Full scan: rebuild the model index on F7 or first use. Future respawns
    -- enter the index through DescendantAdded, so farm ticks do NOT walk Workspace.
    if not state.worldIndexReady or not automatic then
        if not rebuildWorldIndex() then
            state.scanning=false
            return
        end
    end
    -- Rebuild external UI index on manual F7; automated rescans use light PG only.
    rebuildTierGuiIndex(not automatic)
    local models={}
    local rejected=0
    local candidates=0
    for i,model in ipairs(state.worldModels) do
        if not state.alive then state.scanning=false return end
        if plausibleWorldMob(model) then
            candidates+=1
            local er, hp, alive = enemyInfo(model) -- no radius or Y limit
            if er and alive then
                models[#models+1]=model
            else
                rejected+=1
            end
        end
        if i%WORLD_SCAN_YIELD_EVERY==0 then task.wait() end
    end
    table.sort(models, function(a,b)
        local ra, rb = rootOf(a), rootOf(b)
        if not ra or not rb then return a.Name < b.Name end
        return (ra.Position-center).Magnitude < (rb.Position-center).Magnitude
    end)
    state.targets = models
    -- Remember a monster's first observed spawn point, even if the same
    -- Model later gets reused or its root temporarily disappears.
    for _, mob in ipairs(models) do
        local part = rootOf(mob)
        if part and not state.originalSpawns[mob] then
            state.originalSpawns[mob] = part.Position
        end
    end
    local known = false
    for _,m in ipairs(models) do
        if mobIdentity(m) == state.selected then known = true break end
    end
    -- Keep the selected name if the monster is temporarily absent during auto rescan.
    if not known and (not automatic or not state.selected) then
        state.selected = models[1] and mobIdentity(models[1]) or nil
    end
    refreshList()
    state.scanning = false
    info(("ALL LOADED MAP: %d mobs | %d checked | %d excluded%s"):
        format(#models,candidates,rejected,streamingEnabled() and " | STREAMING ON" or ""))
    print("[RE:FINALS V12] Whole-loaded-map enemy scan", #models, "verified", rejected, "excluded; selected", state.selected)
    local unknownSeen={}
    local unknownCount=0
    for _,m in ipairs(models) do
        if mobIdentity(m):find("[Unknown]",1,true) and not unknownSeen[m.Name] then
            unknownSeen[m.Name]=true
            unknownCount=unknownCount+1
            if unknownCount<=4 then
                local examples={}
                for _,desc in ipairs(m:GetDescendants()) do
                    if isGuiText(desc) and desc.Text~="" and #examples<6 then
                        examples[#examples+1]=desc.Name.."="..desc.Text:gsub("[\r\n]"," "):sub(1,45)
                    end
                end
                warn("[RE:FINALS V11][LEVEL DEBUG]",m.Name,
                    "still Unknown. Its own label texts:",table.concat(examples," | "))
            end
        end
    end
    if unknownCount>0 then
        warn("[RE:FINALS V11] Unknown enemy level for",unknownCount,
            "names. If the world labels are not accessible, send F9 LEVEL DEBUG.")
    end
    if #models==0 then
        warn("[RE:FINALS V12] No verified loaded enemies. StreamingEnabled may keep far NPCs unreplicated; never treat unknown allies as enemies.")
    end
end

-- Only proven death/despawn is used to advance; no 2-second countdown.
-- Extra listeners cover common Re:Finals enemy health replication patterns.
-- Store spawn coordinates, not only Model identity: some games recreate a
-- new Model at exactly the same spawn immediately after a kill.
local function spawnKey(model)
    local pos = state.originalSpawns[model]
    if not pos then
        local part = rootOf(model)
        pos = part and part.Position
    end
    if not pos then return nil end
    local function snap(n) return math.floor(n / 7 + 0.5) end
    return mobIdentity(model):lower()..":"..snap(pos.X)..":"..snap(pos.Y)..":"..snap(pos.Z)
end

-- Discover respawned/streamed-in verified enemies for either farm mode.
-- Priority only checks chosen names; selected mode checks the chosen type.
-- This does not reset the active target or the user's priority order.
local function discoverPrioritySpawns()
    if not state.alive or state.scanning or not state.center then return end
    if state.modeAll and #state.priorityOrder==0 then return end
    if not state.modeAll and not state.selected then return end
    local root=playerRoot()
    if not root then return end
    local names={}
    local requested=state.modeAll and state.priorityOrder or {state.selected}
    for _, key in ipairs(requested) do
        local name=key:match("^(.-) %[")
        if name then names[name]=true end
    end
    -- Use the model registry so newly spawned priority-#1 mobs can be found
    -- anywhere in the loaded map, including far outside the old 325-stud ring.
    local existing={}
    for _,model in ipairs(state.targets) do existing[model]=true end
    local added=0
    -- Bucket lookup avoids looping over unrelated scenery models every 0.85s.
    for name in pairs(names) do
        for _,cur in ipairs(state.worldByName[name] or {}) do
            if cur.Parent and cur.Name==name and plausibleWorldMob(cur) and not existing[cur] then
                local mr,_,alive=enemyInfo(cur)
                local identity=mr and mobIdentity(cur)
                local allowed=identity and (state.modeAll
                    and state.priorityRanks[identity] or identity==state.selected)
                if mr and alive and allowed then
                    -- Replace stale same-spawn slots while protecting active model.
                    local key=spawnKey(cur)
                    if key then
                        for j=#state.targets,1,-1 do
                            local old=state.targets[j]
                            if old~=cur and spawnKey(old)==key
                                and (old~=(state.active and state.active.model)) then
                                table.remove(state.targets,j)
                                existing[old]=nil
                            end
                        end
                        state.spawnCooldown[key]=nil
                    end
                    state.targets[#state.targets+1]=cur
                    state.originalSpawns[cur]=mr.Position
                    existing[cur]=true
                    added+=1
                end
            end
        end
    end
    if added>0 then
        state.acquireAfter=0
        state.nextPriorityCheck=0
        refreshList()
        print("[RE:FINALS V12] World respawn discovery:",added,"new selected enemies")
    end
end

-- Returns true for a displayed enemy health value below the near-death threshold.
-- Unlike the Humanoid placeholder HP, this requires an actual X/Y label.
local function nearlyDeadFromEnemyHUD(label)
    if not state.fastNearDeath or not label or not label.Parent then return false end
    local hp,maxHP=parseHealthText(label.Text)
    if not hp or not maxHP or maxHP<=0 then return false end
    return hp>0 and hp <= maxHP * FAST_NEXT_HP_PERCENT / 100
end

local function finishTarget(note, confirmedDead)
    if state.active then
        state.visited[state.active.model] = true
        state.lastTarget = state.active.model
        if confirmedDead then
            state.quickRescanPending = true
            local key = spawnKey(state.active.model)
            if key then
                state.spawnCooldown[key] = os.clock() + DEAD_SPAWN_COOLDOWN
            end
        end
        for _, conn in ipairs(state.active.listeners or {}) do
            if conn.Connected then conn:Disconnect() end
        end
    end
    state.active = nil
    if confirmedDead then state.kills = state.kills + 1 else state.passed = state.passed + 1 end
    if note then
        state.lastSwitchReason=note
        info(note)
    end
end

-- Reserve this forward declaration so health/event callbacks can immediately
-- rotate to the next verified monster, without waiting for the main farm tick.
local requestImmediateNext

local function teleportTo(model)
    local root,char = playerRoot()
    local mobRoot = rootOf(model)
    if not root or not char or not mobRoot then return end
    local offset = root.Position - mobRoot.Position
    if offset.Magnitude <= HIT_DISTANCE then return end
    local direction = offset.Magnitude > 0.1 and offset.Unit or Vector3.new(0,0,1)
    local destination = mobRoot.Position + direction * 4 + Vector3.new(0,1.5,0)
    char:PivotTo(CFrame.lookAt(destination,mobRoot.Position))
end

local function nextTarget()
    local root=playerRoot()
    if not root or not state.center or state.scanning then return end
    local now=os.clock()
    if now<state.acquireAfter then return end
    local candidates=buildSlots()
    local total=#candidates
    local live={}
    local bestRank=math.huge
    for i,m in ipairs(candidates) do
        local key=spawnKey(m)
        if now >= (state.spawnCooldown[key or ""] or 0) then
            local part,_,alive=enemyInfo(m,state.center)
            if part and alive then
                local rank=state.modeAll and state.priorityRanks[mobIdentity(m)] or 1
                if rank then
                    local d=(part.Position-root.Position).Magnitude
                    live[#live+1]={model=m,index=i,rank=rank,distance=d}
                    bestRank=math.min(bestRank,rank)
                end
            end
        end
    end
    -- Rank is the FIRST filter. A previously visited #1 must ALWAYS outrank
    -- any unvisited #2/#3. Visited applies only within that highest live rank.
    local function choose(avoidLast,avoidVisited)
        local chosen=nil
        for _,item in ipairs(live) do
            if item.rank==bestRank
                and (not avoidLast or item.model~=state.lastTarget)
                and (not avoidVisited or not state.visited[item.model]) then
                if not chosen or item.distance<chosen.distance then chosen=item end
            end
        end
        return chosen
    end
    local winner=choose(true,true) or choose(false,true)
    if not winner then
        winner=choose(true,false) or choose(false,false)
        if winner then
            -- New pass only for the current top rank. Do not erase cooldowns.
            for _,item in ipairs(live) do
                if item.rank==bestRank then state.visited[item.model]=nil end
            end
        end
    end
    if not winner then
        state.acquireAfter=now+IDLE_TARGET_RETRY
        if state.waitingSince==0 then state.waitingSince=now end
        return
    end
    local best,index=winner.model,winner.index
    state.waitingSince=0
    state.acquireAfter=now
    state.quickRescanPending=false
    state.rotationIndex=index
    if best then
        local _, hp, _, source, humanoid, label = enemyInfo(best,state.center)
        local target={model=best,lastHP=hp,source=source,highestHP=hp,
            sawDamage=false,dead=false,listeners={},seenUI=label~=nil,hiddenTicks=0,
            watched=setmetatable({}, {__mode="k"}), firstHP=hp,
            acquiredAt=os.clock(), firstAttackAt=nil, rapidCheckAt=0}
        state.active=target
        -- Warp as soon as target is acquired, including inside a death callback.
        teleportTo(best)
        info("Target: "..best.Name.." | HP "..math.floor(hp).." | "..tostring(source))
        if humanoid then
            target.listeners[#target.listeners+1] = humanoid.Died:Connect(function()
                target.dead=true
                requestImmediateNext(target,"Humanoid.Died",true)
            end)
            -- Some games update Humanoid.Health before Died or before the HUD.
            target.listeners[#target.listeners+1] = humanoid.HealthChanged:Connect(function(newHealth)
                if state.active==target and newHealth<=0 then
                    requestImmediateNext(target,"Humanoid.Health=0",true)
                end
            end)
        end
        -- Some enemies expose health as a child NumberValue/IntValue rather
        -- than Model attributes, and the GUI may update a second or two later.
        for _, hpName in ipairs({"HealthReal","CurrentHealth","Health","HP"}) do
            local valueObj = best:FindFirstChild(hpName)
            if valueObj and (valueObj:IsA("NumberValue") or valueObj:IsA("IntValue")) then
                target.listeners[#target.listeners+1] = valueObj.Changed:Connect(function(value)
                    if state.active~=target or type(value)~="number" then return end
                    if value<target.lastHP then target.sawDamage=true end
                    if value<=0 then
                        requestImmediateNext(target, hpName.." Value=0",true)
                    end
                end)
            end
        end
        -- Health attributes can change before the polling loop sees them.
        for _,key in ipairs({"HealthReal","CurrentHealth","Health","HP","Dead","IsDead"}) do
            local previousAttribute = best:GetAttribute(key)
            target.listeners[#target.listeners+1] = best:GetAttributeChangedSignal(key):Connect(function()
                if state.active ~= target then return end
                if key == "Dead" or key == "IsDead" then
                    if best:GetAttribute(key)==true then
                        requestImmediateNext(target,key.."=true",true)
                    end
                    return
                end
                local value=best:GetAttribute(key)
                if type(value)~="number" then return end
                local oldValue = previousAttribute
                previousAttribute = value
                if type(oldValue)=="number" and value<oldValue then target.sawDamage=true end
                if value<=0 then
                    -- Trust a real positive-to-zero transition even if the HUD still shows old HP.
                    -- A permanently stale zero attribute alone is NOT proof of death.
                    if type(oldValue)=="number" and oldValue>0 then
                        requestImmediateNext(target,key.." changed to 0",true)
                    end
                elseif target.sawDamage and value>target.lastHP*1.4
                    and value>=target.highestHP*0.80 then
                    requestImmediateNext(target,key.." respawn reset",true)
                end
            end)
        end
        if label and label.Parent then
            target.listeners[#target.listeners+1] = label:GetPropertyChangedSignal("Text"):Connect(function()
                if state.active ~= target then return end
                local current=parseHealthText(label.Text)
                if not current then return end
                if current < target.lastHP then target.sawDamage=true end
                if current<=0 then
                    requestImmediateNext(target,"HP bar zero",true)
                elseif target.sawDamage and state.fastNearDeath and nearlyDeadFromEnemyHUD(label) then
                    requestImmediateNext(target,"FAST NEXT: HP <=1%",false)
                elseif target.sawDamage and current>target.lastHP*1.4
                    and current>=target.highestHP*0.80 then
                    requestImmediateNext(target,"HP bar respawn reset",true)
                end
                target.lastHP=current
            end)
            target.listeners[#target.listeners+1] = label:GetPropertyChangedSignal("Visible"):Connect(function()
                if state.active==target and not label.Visible and target.sawDamage then
                    requestImmediateNext(target,"HP bar hidden after damage",true)
                end
            end)
            local billboard = label:FindFirstAncestorWhichIsA("BillboardGui")
            if billboard then
                target.listeners[#target.listeners+1] = billboard:GetPropertyChangedSignal("Enabled"):Connect(function()
                    if state.active==target and not billboard.Enabled and target.sawDamage then
                        requestImmediateNext(target,"HP billboard disabled",true)
                    end
                end)
            end
        end
        target.listeners[#target.listeners+1] = best.AncestryChanged:Connect(function()
            if state.active==target and not best:IsDescendantOf(workspace) then
                requestImmediateNext(target,"enemy removed",true)
            end
        end)
        target.listeners[#target.listeners+1] = best.Destroying:Connect(function()
            if state.active==target then
                requestImmediateNext(target,"enemy destroyed",true)
            end
        end)
        -- The body may disappear before model cleanup / HP HUD refresh.
        -- Only trust this after recorded damage to avoid despawn/LOD false positives.
        local bodyRoot = rootOf(best)
        if bodyRoot then
            target.listeners[#target.listeners+1] = bodyRoot:GetPropertyChangedSignal("Transparency"):Connect(function()
                if state.active==target and target.sawDamage
                    and bodyRoot.Transparency >= 0.99 then
                    requestImmediateNext(target,"body hidden after damage",false)
                end
            end)
        end

        -- V6: Watch every *existing* HP widget/value under this verified enemy.
        -- Older versions watched only the first HP label. In Re:Finals that
        -- label can be a delayed billboard while another bar changes immediately.
        local function watchEnemyDescendant(obj)
            if target.watched[obj] or #target.listeners>=120 then return end
            local low=obj.Name:lower()
            if obj:IsA("TextLabel") then
                local cur,maxHP=parseHealthText(obj.Text)
                if not cur or not maxHP then return end
                target.watched[obj]=true
                local prior=cur
                target.listeners[#target.listeners+1]=obj:GetPropertyChangedSignal("Text"):Connect(function()
                    if state.active~=target then return end
                    local current,full=parseHealthText(obj.Text)
                    if not current or not full then return end
                    if current<prior then target.sawDamage=true end
                    prior=current
                    if current<=0 then
                        requestImmediateNext(target,"HP text reached zero",true)
                    elseif target.sawDamage and state.fastNearDeath
                        and current<=full*FAST_NEXT_HP_PERCENT/100 then
                        requestImmediateNext(target,"FAST NEXT: HUD <=1%",false)
                    end
                end)
            elseif (obj:IsA("NumberValue") or obj:IsA("IntValue"))
                and (low=="hp" or low=="health" or low=="healthreal" or low=="currenthealth") then
                target.watched[obj]=true
                local prior=obj.Value
                target.listeners[#target.listeners+1]=obj.Changed:Connect(function(v)
                    if state.active~=target or type(v)~="number" then return end
                    if v<prior then target.sawDamage=true end
                    prior=v
                    if v<=0 then requestImmediateNext(target,"nested HP value zero",true) end
                end)
            elseif obj:IsA("Frame")
                and (low=="healthfill" or low=="hpfill" or low=="healthbarfill") then
                target.watched[obj]=true
                local initialScale=obj.Size.X.Scale
                local initialOffset=obj.Size.X.Offset
                target.listeners[#target.listeners+1]=obj:GetPropertyChangedSignal("Size"):Connect(function()
                    if state.active~=target then return end
                    local sx,ox=obj.Size.X.Scale,obj.Size.X.Offset
                    if target.sawDamage and (initialScale>0.05 and sx<=0.002
                        or initialOffset>8 and ox<=1) then
                        requestImmediateNext(target,"HP fill empty",true)
                    end
                end)
            end
        end
        for _,desc in ipairs(best:GetDescendants()) do
            watchEnemyDescendant(desc)
        end
        target.listeners[#target.listeners+1]=best.DescendantAdded:Connect(function(desc)
            if state.active==target then watchEnemyDescendant(desc) end
        end)
        -- Detect models that visually disappear without changing Humanoid HP.
        -- Only consider parts that were visibly rendered before combat.
        local originalVisibleParts={}
        for _,desc in ipairs(best:GetDescendants()) do
            if desc:IsA("BasePart") and desc.Name~="HumanoidRootPart"
                and desc.Transparency<0.8 then
                originalVisibleParts[#originalVisibleParts+1]=desc
            end
        end
        local function checkBodyGone()
            if state.active~=target or not target.sawDamage or #originalVisibleParts<2 then return end
            local hidden=0
            for _,part in ipairs(originalVisibleParts) do
                if not part:IsDescendantOf(best) or part.Transparency>=0.98 then hidden+=1 end
            end
            if hidden >= math.ceil(#originalVisibleParts*0.85) then
                requestImmediateNext(target,"visible enemy body disappeared",true)
            end
        end
        for _,part in ipairs(originalVisibleParts) do
            if #target.listeners>=140 then break end
            target.listeners[#target.listeners+1]=part:GetPropertyChangedSignal("Transparency"):Connect(checkBodyGone)
        end
        target.listeners[#target.listeners+1]=best.DescendantRemoving:Connect(function(desc)
            if state.active~=target or not target.sawDamage then return end
            if target.watched[desc] and desc:IsA("TextLabel") then
                requestImmediateNext(target,"enemy HP label removed",false)
            elseif desc:IsA("BasePart") then
                task.defer(checkBodyGone)
            end
        end)
    end
end

-- Both NEXT MOB and automatic transitions use EXACTLY this path.
-- This avoids the old event-only route whose trigger could arrive ~2 seconds late.
local function advanceSameAsNext(reason, confirmedDead, skipSpawnSeconds)
    local previous = state.active and state.active.model
    local oldKey = previous and spawnKey(previous)
    if state.active then finishTarget(reason, confirmedDead) end
    if skipSpawnSeconds and oldKey then
        state.spawnCooldown[oldKey] = math.max(state.spawnCooldown[oldKey] or 0,
            os.clock() + skipSpawnSeconds)
    end
    state.acquireAfter = 0
    nextTarget() -- same function as the manual NEXT MOB button
    return previous, state.active and state.active.model
end

-- Always interrupt a lower-priority target when a higher-priority
-- selected monster is confirmed alive. Uses the same fast teleport path
-- as the manual NEXT MOB button; does not wait for #2 to finish.
local function tryPriorityPreempt(target,now)
    if not state.modeAll or #state.priorityOrder==0 or state.transitioning
        or state.active~=target or now<state.nextPriorityCheck then return false end
    state.nextPriorityCheck=now+0.10
    local activeRank=state.priorityRanks[mobIdentity(target.model)] or math.huge
    if activeRank<=1 then return false end
    for _, model in ipairs(state.targets) do
        local rank=state.priorityRanks[mobIdentity(model)]
        if rank and rank<activeRank and model~=target.model then
            local key=spawnKey(model)
            if now>=(state.spawnCooldown[key or ""] or 0) then
                local part,_,alive=enemyInfo(model,state.center)
                if part and alive then
                    local prior,after=advanceSameAsNext(
                        "PRIORITY RESPAWN: #"..rank.." "..mobIdentity(model),false)
                    if after and after~=prior then
                        print("[RE:FINALS V11] PREEMPT:",
                            prior and mobIdentity(prior) or "none","->",mobIdentity(after))
                        return true
                    end
                end
            end
        end
    end
    return false
end

-- Can we actually rotate to ANOTHER verified, living monster in the selected
-- group? Never jump to allies, NPCs, or the currently attacked spawn.
local function hasOtherLivingTarget(current)
    if not current or not state.center or state.scanning then return false end
    local now = os.clock()
    for _, model in ipairs(buildSlots()) do
        if model ~= current and model.Parent then
            local key = spawnKey(model)
            if now >= (state.spawnCooldown[key or ""] or 0) then
                local mobRoot, _, alive = enemyInfo(model, state.center)
                if mobRoot and alive then return true end
            end
        end
    end
    return false
end

-- The game can keep the 100B/100B enemy billboard/model around after a
-- one-hit kill. Waiting for its replicated death is why earlier versions
-- stalled even though manually pressing NEXT MOB teleported instantly.
-- When RAPID is enabled, treat the chosen interval as a maximum dwell time.
-- This is a deliberate attack-speed tradeoff: it CAN leave a mob alive.
local function tryRapidRotation(tracked, char, now)
    local delay = RAPID_DELAYS[state.rapidIndex]
    if delay == 0 or not state.farming or state.active ~= tracked or state.transitioning then return false end
    if now < (tracked.rapidCheckAt or 0) then return false end
    -- If using Tool combat, start the dwell timer on the FIRST actual
    -- Tool:Activate() for this target, not on teleport (Tool cooldown matters).
    local hasTool = char and char:FindFirstChildOfClass("Tool") ~= nil
    if hasTool and not tracked.firstAttackAt then return false end
    local startAt = tracked.firstAttackAt or tracked.acquiredAt or now
    if now - startAt < delay then return false end
    tracked.rapidCheckAt = now + RAPID_CHECK_INTERVAL
    -- Do not abandon a single living mob if there is nowhere to go.
    if not hasOtherLivingTarget(tracked.model) then return false end
    local oldName = tracked.model.Name
    local elapsed = now - startAt
    local prev, dest = advanceSameAsNext("RAPID ROTATE after "..string.format("%.2f",elapsed).."s (not death-confirmed)",
        false, math.max(RAPID_SPAWN_SKIP,delay*2.5))
    if dest and dest ~= prev then
        state.rapidSwitches += 1
        print(("[RE:FINALS V11] RAPID %s -> %s, dwell %.3fs (HP event not required)")
            :format(oldName, dest.Name, elapsed))
        return true
    end
    return false
end

requestImmediateNext = function(target, why, confirmed)
    if not state.alive or not state.farming or state.active~=target or state.transitioning then return end
    state.transitioning = true
    task.defer(function()
        if state.alive and state.farming and state.active == target then
            local ok,err = pcall(function()
                local start = os.clock()
                local previous, dest = advanceSameAsNext(target.model.Name.." "..why.." -> NEXT", confirmed)
                print(("[RE:FINALS V11] DEATH %s -> %s | %s | move %.3fs")
                    :format(previous and previous.Name or "?", dest and dest.Name or "none", why, os.clock()-start))
            end)
            if not ok then warn("[RE:FINALS V11] transition error:",err) end
        end
        state.transitioning = false
    end)
end

local function toolAttack(character)
    if os.clock()-state.lastAttack < TOOL_COOLDOWN then return end
    state.lastAttack = os.clock()
    local tool = character:FindFirstChildOfClass("Tool")
    if not tool then
        state.attackNote = "NO TOOL: game-specific attack needed"
        return
    end
    local ok,err = pcall(function() tool:Activate() end)
    if ok and state.active and not state.active.firstAttackAt then
        state.active.firstAttackAt = os.clock()
    end
    state.attackNote = ok and ("Tool:"..tool.Name) or ("Tool error:"..tostring(err):sub(1,40))
end

local function step()
    local root,char=playerRoot()
    if not root or not char then return end
    local now=os.clock()
    -- World-wide farming deliberately crosses long distances; no 415-stud
    -- zone-change detector here. The user can press F7 to scan a new world.
    if state.worldIndexReady and now >= state.nextWorldPrune then
        pruneWorldIndex()
    end
    if not state.farming or state.scanning then return end
    if not state.center then scanHere(false) return end
    if state.modeAll and #state.priorityOrder==0 then
        if state.active then forgetActive() end
        if now-state.lastMessageTime>1 then
            state.lastMessageTime=now
            info("FARM QUEUE EMPTY: open menu and ADD desired monster types")
        end
        return
    end
    -- Discover new selected mobs anywhere in the loaded Workspace. In priority
    -- mode the check is most useful while fighting a lower-ranked target.
    if now>=state.nextPriorityDiscovery and
        ((state.modeAll and #state.priorityOrder>0) or (not state.modeAll and state.selected)) then
        state.nextPriorityDiscovery=now+0.85
        if state.active and state.modeAll then
            local activeRank=state.priorityRanks[mobIdentity(state.active.model)] or math.huge
            if activeRank>1 then discoverPrioritySpawns() end
        else
            discoverPrioritySpawns()
        end
    end
    if state.active and state.modeAll
        and not state.priorityRanks[mobIdentity(state.active.model)] then
        forgetActive()
    end
    if not state.active and not state.transitioning then nextTarget() end
    if not state.active then
        -- If the cached list has no other live monster after a kill, allow
        -- one prompt area rescan to discover other spawns, not endless scans.
        if state.quickRescanPending and now-state.lastScan >= 0.55 then
            state.quickRescanPending = false
            scanHere(true)
        elseif now-state.lastScan>=RESCAN_WHEN_EMPTY then
            scanHere(true) -- slow fallback after the one prompt scan
        end
        return
    end
    local tracked=state.active
    local model=tracked.model
    if not model or not model:IsDescendantOf(workspace) then
        requestImmediateNext(tracked,"enemy despawned",true)
        return
    end
    local mr,hp,alive,source,humanoid,label=enemyInfo(model,state.center)
    if tracked.dead or (hp~=nil and hp<=0) or (humanoid and humanoid.Health<=0)
        or model:GetAttribute("Dead")==true or model:GetAttribute("IsDead")==true then
        requestImmediateNext(tracked,"detected dead",true)
        return
    end
    if not mr or alive==false then
        requestImmediateNext(tracked,"invalid target",false)
        return
    end
    -- Many games reuse the same model when respawning. Detect a health reset
    -- AFTER observed damage as the end of the previous monster life.
    if source==tracked.source and type(hp)=="number" then
        if hp<tracked.lastHP then tracked.sawDamage=true end
        if tracked.sawDamage and hp>tracked.lastHP*1.4 and hp>=tracked.highestHP*0.80 then
            requestImmediateNext(tracked,"HP reset",true)
            return
        end
        tracked.highestHP=math.max(tracked.highestHP,hp)
    else
        tracked.source=source
        tracked.sawDamage=false
        tracked.highestHP=hp
    end
    tracked.lastHP=hp
    if tracked.sawDamage and nearlyDeadFromEnemyHUD(label) then
        requestImmediateNext(tracked,"FAST NEXT: HP <=1%",false)
        return
    end
    if label and label.Parent then
        if not label.Visible or (label:FindFirstAncestorWhichIsA("BillboardGui")
            and not label:FindFirstAncestorWhichIsA("BillboardGui").Enabled) then
            tracked.hiddenTicks = tracked.hiddenTicks + 1
            if tracked.hiddenTicks>=3 and tracked.sawDamage then
                requestImmediateNext(tracked,"HP bar hidden",true)
                return
            end
        else tracked.hiddenTicks=0 end
    end
    -- Strict priority has precedence over RAPID / current target dwell time.
    if tryPriorityPreempt(tracked,now) then return end
    -- Fall back to the manual NEXT path if the HP/death notice is late.
    -- Check after all confirmed-death checks so real death always wins.
    if tryRapidRotation(tracked, char, now) then return end
    local pos=mr.Position
    local offset=root.Position-pos
    if offset.Magnitude>HIT_DISTANCE then
        local direction=offset.Magnitude>0.1 and offset.Unit or Vector3.new(0,0,1)
        local destination=pos+direction*4+Vector3.new(0,1.5,0)
        char:PivotTo(CFrame.lookAt(destination,pos))
    end
    toolAttack(char)
    if now-state.lastMessageTime>=0.45 then
        state.lastMessageTime=now
        info(("%s HP:%.0f (%s) | %s | K:%d | skip:%d"):
            format(model.Name,hp,source or "?",state.attackNote,state.kills,state.passed))
    end
end

function state.stop()
    if not state.alive then return end
    state.alive = false
    state.farming = false
    forgetActive()
    for _,c in ipairs(connections) do
        if c.Connected then c:Disconnect() end
    end
    if gui.Parent then gui:Destroy() end
    if sharedEnv.__RE_FINALS_LOCAL_FARM_BETA == state then
        sharedEnv.__RE_FINALS_LOCAL_FARM_BETA = nil
    end
end
addConnection(minimizeBtn.Activated:Connect(toggleMinimize))
addConnection(closeBtn.Activated:Connect(function() state.stop() end))
addConnection(scanBtn.Activated:Connect(function() scanHere(false) end))
local function toggleMode()
    state.modeAll = not state.modeAll
    state.visited = {}; state.rotationIndex = 0; state.acquireAfter = 0; forgetActive()
    modeBtn.Text=state.modeAll and "MODE: PRIORITY ONLY (F5)" or "MODE: SELECTED MOB (F5)"
    if state.modeAll then
        info(#state.priorityOrder>0 and "ONLY chosen mobs. #1 preempts when alive."
            or "EMPTY FARM QUEUE: select mobs using ADD first")
    end
end
addConnection(modeBtn.Activated:Connect(toggleMode))
addConnection(farmBtn.Activated:Connect(function()
    state.farming = not state.farming
    farmBtn.Text = state.farming and "TELEPORT FARM: ON (F6)" or "TELEPORT FARM: OFF (F6)"
    if state.farming and not state.center then scanHere(false) end
    if state.farming and state.modeAll and #state.priorityOrder==0 then
        info("FARM QUEUE EMPTY: click FARM QUEUE and ADD monsters")
    end
end))
addConnection(nextBtn.Activated:Connect(function()
    local old, new = advanceSameAsNext("Manual next", false)
    print("[RE:FINALS V11] MANUAL NEXT:", old and old.Name or "none", "->", new and new.Name or "none")
end))
addConnection(fastBtn.Activated:Connect(function()
    state.fastNearDeath=not state.fastNearDeath
    fastBtn.Text=state.fastNearDeath and "FAST NEXT AT 1% HP: ON" or "FAST NEXT AT 1% HP: OFF"
    info(state.fastNearDeath and "Low-HP pre-switch ON (may leave <=1% alive)"
        or "Exact death only: no pre-switch")
end))
local function refreshRapidButton()
    local delay = RAPID_DELAYS[state.rapidIndex]
    rapidBtn.Text = delay == 0 and "RAPID ROTATE: OFF (DEATH ONLY)"
        or ("RAPID ROTATE: %.2fs | CLICK TO CHANGE"):format(delay)
    rapidBtn.BackgroundColor3 = delay == 0
        and Color3.fromRGB(68, 78, 94) or Color3.fromRGB(36, 96, 103)
end
addConnection(rapidBtn.Activated:Connect(function()
    state.rapidIndex = state.rapidIndex % #RAPID_DELAYS + 1
    refreshRapidButton()
    local delay = RAPID_DELAYS[state.rapidIndex]
    info(delay == 0 and "Rapid OFF: wait for confirmed death"
        or ("Rapid %.2fs: skips alive enemies if attack is slower. Use 0.65/1.00 if needed."):format(delay))
end))
refreshRapidButton()
refreshPriorityUI()
addConnection(UIS.InputBegan:Connect(function(input, used)
    if not state.alive or input.UserInputType ~= Enum.UserInputType.Keyboard then return end
    local key = input.KeyCode
    if state.waitingForHotkey then
        if key == Enum.KeyCode.Escape then
            state.waitingForHotkey = false
            updateHideKeyLabel()
            info("Hotkey change canceled; current key: "..state.hideKeyName)
            return
        end
        if key == Enum.KeyCode.F5 or key == Enum.KeyCode.F6
            or key == Enum.KeyCode.F7 or key == Enum.KeyCode.F8
            or key == Enum.KeyCode.Unknown then
            hideKeyBtn.Text = "RESERVED KEY; PRESS ANOTHER (ESC CANCEL)"
            return
        end
        state.hideKeyName = key.Name
        sharedEnv.__RE_FINALS_V9_HIDE_KEY = key.Name
        state.waitingForHotkey = false
        updateHideKeyLabel()
        info("GUI hide/show hotkey changed to " .. key.Name)
        print("[RE:FINALS V11] GUI hotkey rebound to", key.Name)
        return -- Binding a key must NOT also hide the GUI immediately.
    end
    if key.Name == state.hideKeyName then
        -- Always allow restoring a hidden GUI, even if the game consumes input.
        -- Avoid toggling while the player is typing in any Roblox TextBox.
        if UIS:GetFocusedTextBox() then return end
        setGuiHidden(not state.guiHidden)
        return
    end
    if used then return end
    if key == Enum.KeyCode.F5 then toggleMode()
    elseif input.KeyCode == Enum.KeyCode.F6 then
        state.farming = not state.farming
        farmBtn.Text = state.farming and "TELEPORT FARM: ON (F6)" or "TELEPORT FARM: OFF (F6)"
        if state.farming and not state.center then scanHere(false) end
    elseif input.KeyCode == Enum.KeyCode.F7 then scanHere(false)
    elseif input.KeyCode == Enum.KeyCode.F8 then state.stop() end
end))
-- Manual dragging, no modal mouse capture.
local dragging, startMouse, startFrame = false, nil, nil
addConnection(header.InputBegan:Connect(function(i)
    if i.UserInputType == Enum.UserInputType.MouseButton1 then
        dragging=true; startMouse=i.Position; startFrame=frame.Position
    end
end))
addConnection(UIS.InputChanged:Connect(function(i)
    if dragging and i.UserInputType == Enum.UserInputType.MouseMovement then
        local d=i.Position-startMouse
        frame.Position=UDim2.fromOffset(startFrame.X.Offset+d.X,startFrame.Y.Offset+d.Y)
    end
end))
addConnection(UIS.InputEnded:Connect(function(i)
    if i.UserInputType==Enum.UserInputType.MouseButton1 then dragging=false end
end))
task.spawn(function()
    while state.alive and gui.Parent do
        local ok,err = pcall(step)
        if not ok then warn("[RE:FINALS]",err); info("ERROR "..tostring(err):sub(1,90)) end
        task.wait(state.farming and TICK or 0.7)
    end
end)
print("[RE:FINALS V12] WHOLE LOADED MAP + STRICT PRIORITY + RAPID 0.45s | StreamingEnabled:", streamingEnabled(), "| hide:", state.hideKeyName, "| F5 F6 F7 F8")

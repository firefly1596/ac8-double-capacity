-- HD2-Addon: mods/starm/autocannon_capacity

-- ===========================================================================
--  AC-8 机炮：背包弹夹 10 -> 20（100 发）；每次补给 5 -> 10 夹
--
--  v5.0.0（2026-10-05）—— **锚定方式回归到被实测验证过两次的路**：
--
--    1. 分帧枚举内存区域，按"私有/已提交 + 开头 28 字节 == EntityManager
--       map_header"锚定 EntityManager（尺寸只记日志、不做判据 ——
--       尺寸随状态变，我踩过 46616576 vs 98586624 的坑；
--       我的 profile 探针在两个独立会话里都采到 header=70cac180... 的 EM，
--       m-103 V1.35 也用同一组常量）。
--    2. 表偏移（两次探针会话间完全一致）：
--         WeaponRoundsComponentData  EM+5766100  头 dlsum=0x66081072（仅校验记录用）
--         DepositComponentData       EM+7287348  头 dlsum=0xC435BA85
--       主路径固定偏移校验表头；失配时**只在 EM 内**（46MB，切片）按
--       'LDLD'+dlsum 搜索 —— 不出 EM、不扫全地址空间。
--    3. 记录定位：Deposit 表体（~5.5KB）整读后做 152 字节模板匹配：
--         == original(0.2.1 实测)  → 打补丁
--         == modified(+0=20,+8=10) → 已生效，地址进看门狗（幂等）
--         只有中段(FFFFFFFF+8B标记) → 逐字段判定：+0∈{10,20} 且 +8∈{5,10}
--           才修，否则整条拒绝并 dump 行 hex。
--
--  ── 为什么这么走（三个失败版本的直接证据）─────────────────────────
--  * v3.x 指针链 `*(game+owner_rva)`：A 能读到，但它在 98MB 区域 +776 处，
--    我却拿"区域尺寸"当身份判据 → 全部误报；表也不在该固定偏移。
--  * v4.0.0 Core(candidate_slot)：**0.2.1 新包的 candidate_slot=15799208 是
--    旧构建(24826606)漏更的值** —— 新包 owner_rva/map/record_size/record_index
--    全换新，唯独 candidate_slot 与旧包一字不差；运行时读出 nil/0x0。
--    同会话别的 Core mod 槽位在 -13.6M(Stalwart) / +58.4M(Pacifier、cookout)
--    两个簇，15.8M 哪个都不在 → 正是排错表 B 类"指针槽 RVA 变了"。
--  * link_diag 的 ±64MB 槽位扫描 = 1677 万次 RPM → 游戏崩溃。
--    本版全程读取 ~几千次以内，全部 os.clock(2ms) 切片。
--
--  ── 帧率 ─────────────────────────────────────────────────────────
--    工作态每 2 帧唤醒（每步 2ms 硬预算）；稳态每 60 帧看门狗
--    （2 个地址 + 表头，直读）。构建锁：game.dll SHA-256 不符一字不写。
--
--  ── v6.0.0：补齐"20 发弹仓"的适配（原作者完整 4 处配方）────────────────
--  原作者 README：'Original five-round loading increments ... retained;
--                 top-up threshold adjusted for the larger magazine.'
--  实测记录：+72=10.0f 上限 / +92=5 装填步长 / +96=6.0f **补弹阈值**。
--  0.2.1 两包的 rounds edits = {+72→20.0f, +96→4.0f}；我们此前只改了 +72 ——
--  上限到 20 但阈值仍是原版 6.0，与大弹仓不匹配（换弹最多补到 10 的原因）。
--  本版把 +96: 6.0f → 4.0f 按原作者原值补齐，四个编辑与 0.2.1 完全一致：
--    rounds +72: 10.0f→20.0f   rounds +96: 6.0f→4.0f
--    deposit +0: 10→20         deposit +8: 5→10
--
--  产出：%LOCALAPPDATA%\CowboyBingus\Helldivers2\Logs\AutocannonCapacity.log
--        %LOCALAPPDATA%\CowboyBingus\Helldivers2\Logs\AutocannonCapacity_STATUS.log
-- ===========================================================================

local MOD_KEY = 'StarmAutocannonCapacity'
if rawget(_G, MOD_KEY) then return rawget(_G, MOD_KEY) end

local M = {
  version  = '1.0.0',
  phase    = 'loaded',
  frame    = 0,
  armed    = false,
  hooked   = false,
  writes   = 0,
  refusals = 0,
  errs     = 0,
  -- 所有参与算术/比较的字段都在构造器里声明（漏一个 = 对 nil 运算，
  -- 被 pcall 吞掉后表现成"完全没生效"——这个错犯过四次）
  rounds      = 0,
  waits       = 0,
  due_frame   = 0,
  enum_addr   = 0x10000,
  enum_done   = false,
  enum_count  = 0,
  gaps        = 0,
  cand        = {},   -- 必须是表：第一个候选就索引它，nil 会直接抛错
  head_i      = 1,
  em          = nil,
  em_size     = 0,
  dep_addr    = nil,
  dep_off     = 7287348,
  rounds_addr   = nil,
  rounds_checked = false,
  dep_off_src = 'fixed',
  scan_cursor = 0,
  scan_done   = false,
  written     = nil,
  checks      = 0,
}

rawset(_G, MOD_KEY, M)

-- ------------------------------------------------------------------ 日志
local out = {}
local function add(line)
  out[#out + 1] = line
  if #out > 3000 then table.remove(out, 1) end
end

local function dump(name, text)
  pcall(function()
    local loader = rawget(_G, 'CowboyBingusModLoader')
    local f = loader and loader.open_log and loader.open_log(name)
    if f then f:write(text); f:close() end
  end)
end

local function status_text()
  local n = 0
  if M.written then for _ in pairs(M.written) do n = n + 1 end end
  local first
  if n > 0 and M.phase == 'patched' then
    first = ('OK - 补丁生效中（%d 处）'):format(n)
  elseif M.phase == 'failed' then
    first = '失败 - ' .. tostring(M.fail_reason)
  else
    first = '运行中 - ' .. tostring(M.phase)
  end
  return table.concat({
    first,
    'revision=' .. M.version,
    'phase=' .. tostring(M.phase),
    'updated=' .. os.date('%Y-%m-%d %H:%M:%S'),
    ('帧=%d armed=%s EM=%s Deposit表=%s(+%d,%s)')
      :format(M.frame, tostring(M.armed),
              M.em and ('0x%X'):format(M.em) or '未锚定',
              M.dep_addr and ('0x%X'):format(M.dep_addr) or '未定位',
              M.dep_off, M.dep_off_src),
    ('定位轮次=%d 等待=%d 写入=%d 拒绝=%d 错误=%d 看门狗复核=%d 已生效地址=%d')
      :format(M.rounds, M.waits, M.writes, M.refusals, M.errs, M.checks, n),
    '方法=EM 枚举锚定 + 表头校验 + 152B 记录模板比对（不扫全地址空间、不依赖 candidate_slot）',
    '目标：弹仓 10->20 发；补弹阈值 16.0f（= 容量-4，用户实测规律）；背包 10->20、补给 5->10',
  }, '\n') .. '\n'
end

local function flush_all()
  dump('AutocannonCapacity.log', table.concat(out, '\n') .. '\n')
  dump('AutocannonCapacity_STATUS.log', status_text())
end

-- ------------------------------------------------------------------ 环境闸门
local loader = rawget(_G, 'CowboyBingusModLoader')
if type(loader) ~= 'table' or tonumber(loader.api) ~= 1
   or type(loader.open_log) ~= 'function' then
  M.phase = 'failed'
  M.fail_reason = 'unsupported_loader'
  add('loader/API 不符，静默退出（未挂钩子、未用 ffi）')
  flush_all()
  return M
end

-- ------------------------------------------------------------------ 常量
local ARM_FRAME      = 120
local SCAN_CADENCE   = 2
local STEADY_CADENCE = 60
local BUDGET         = 0.002
local ENUM_PER_SLICE = 4096
local RECHECK_EVERY  = 300
local BACKOFF        = { 2, 4, 8, 16, 30, 60 }   -- 秒；上限后固定 60 秒，永不彻底放弃
local MAX_BACKOFF_N  = #BACKOFF
local FALLBACK_PER_SLICE = 16
local FALLBACK_CHUNK = 64 * 1024
local CAND_MAX_SIZE  = 1024 * 1024 * 1024
local CAND_MIN_SIZE  = 4 * 1024 * 1024

local MODULE_SHA256 =
  '2e2c3b7c2500646dadd5f2b4c6e0504dbb7e7896139f64cddc0d1813c718f51e'

local PB_MAP_HEADER  = '70cac1804c444c440100000070cac18084d002000100000000000000'
local PB_EM_SIZE_HINT = 46616576   -- 只记日志

local ROUNDS_OFF = 5766100        -- 仅做信息性校验（本轮不写弹仓）
local DEP_HASH   = 0xC435BA85

-- WeaponRoundsComponentData（与 Deposit 同一 EM 内的另一张表）
local ROUNDS_OFF  = 5766100
local ROUNDS_HDR  = '4c444c440100000072100866f0100000010000000000000000000000'
local ROUNDS_HASH = 0x66081072        -- djb2("WeaponRoundsComponentData")
local ROUNDS_HASH_LE = string.char(0x72, 0x10, 0x08, 0x66)
local ROUNDS_MAPLEN   = 800           -- 0.2.1 SPEC 的 #hashmap
local ROUNDS_INDEX    = 23            -- record_index（0.2.1 SPEC）
local ROUNDS_SIZE     = 136     -- djb2("DepositComponentData")
local DEP_HASH_LE = string.char(0x85, 0xBA, 0x35, 0xC4)

-- Deposit 行（0.2.1 包实测 152B）：中段 = +4 FFFFFFFF + +12 8B 标记
-- 记录内布局：+4=FFFFFFFF  +8=旧/目标字段(4B)  +12..19=8B 标记
-- 旧代码把 FFFFFFFF+标记 当连续 12 字节是错的（中间隔着 +8 字段）；
-- 正确做法：按 **8B 标记**定位，记录起点 = 命中处 - 12。
local DEP_MARK = string.char(0x36, 0x62, 0xA7, 0x0B, 0x1C, 0xE3, 0xF8, 0xBD)
local RECORD_SIZE = 152

-- 两组编辑：按记录分开，recheck 按绑定的 (表类型, 偏移) 查找
local R_EDITS = {
  { off = 72, old = string.char(0x00, 0x00, 0x20, 0x41),   -- 10.0f
              tgt = string.char(0x00, 0x00, 0xA0, 0x41),   -- 20.0f
    label = '弹仓上限 feed_capacity_1',  desc = '10.0f -> 20.0f' },
  { off = 96, old = string.char(0x00, 0x00, 0xC0, 0x40),   -- 6.0f（原版）
              olds = { string.char(0x00, 0x00, 0xC0, 0x40),   -- 6.0f 原版
                       string.char(0x00, 0x00, 0x80, 0x40),   -- 4.0f（6.0.0）
                       string.char(0x00, 0x00, 0xA0, 0x41) }, -- 20.0f（6.1.0 若跑过）
              tgt = string.char(0x00, 0x00, 0x80, 0x41),   -- 16.0f  规律=容量-4
    label = '补弹阈值 top-up threshold', desc = '-> 16.0f（rounds<16 可补）' },
}
local D_EDITS = {
  { off = 0,  old = string.char(0x0A, 0x00, 0x00, 0x00),   -- 10
              tgt = string.char(0x14, 0x00, 0x00, 0x00),   -- 20
    label = '背包弹夹数 capacity',    desc = '10 -> 20' },
  { off = 8, old = string.char(0x05, 0x00, 0x00, 0x00),   -- 5
              tgt = string.char(0x0A, 0x00, 0x00, 0x00),   -- 10
    label = '每次补给 refill_amount', desc = '5 -> 10' },
}

local DEP_ORIG_HEX = '0a000000ffffffff050000003662a70b1ce3f8bd000000000000000000000000'
  .. '0000000000000000000000002ac8fe9e6ce3de248037336177e7d614b52757b1'  .. '76846f0a1bb8b78a885a6eb1822ecee27159c475000000000000000000000000'  .. '0000000000000000000000000000000000000000000000000000000000000000'  .. '01000000000000005f5c0b6f31fbcfa858bda44b00000000'

local api = nil

local function unhex(s)
  local t = {}
  for i = 1, #s, 2 do t[#t + 1] = string.char(tonumber(s:sub(i, i + 1), 16)) end
  return table.concat(t)
end

local function u32(b, o)
  local a, c, d, e = b:byte(o + 1, o + 4)
  if not a then return nil end
  return a + c * 256 + d * 65536 + e * 16777216
end

local function hex(b)
  return (b:gsub('.', function(c) return string.format('%02x', c:byte()) end))
end

-- rounds 记录（136B，0.2.1 SPEC original）与"已按 v6.0.0 改过"的模板
local R_ORIG_HEX = '0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f0000803f73000000000000000000204100000000000000000000000000000000050000000000c040000000000100000000000000000000000000000000000000000000000000000000000000'
local R_ORIG = unhex(R_ORIG_HEX)
local R_MOD  = R_ORIG:sub(1, 72) .. unhex('0000a041') .. R_ORIG:sub(77, 96)
                .. unhex('00008041') .. R_ORIG:sub(101)
assert(#R_ORIG == 136 and #R_MOD == 136, 'rounds template size')
-- 6.2.0 目标态：72 -> 20.0f, 96 -> 16.0f（规律：阈值 = 容量 - 4）
local R_TGT = R_ORIG:sub(1, 72) .. unhex('0000a041') .. R_ORIG:sub(77, 96)
               .. unhex('00008041') .. R_ORIG:sub(101)
assert(#R_TGT == 136, 'rounds target size')
-- 6.1.0 已部署态（若跑过）：72 -> 20.0f, 96 -> 20.0f
local R_MOD20 = R_ORIG:sub(1, 72) .. unhex('0000a041') .. R_ORIG:sub(77, 96)
                 .. unhex('0000a041') .. R_ORIG:sub(101)
assert(#R_MOD20 == 136, 'rounds mod20 size')
-- 模板已知态：原版 / 6.0.0(96=4) / 6.1.0(96=20) / 目标(96=16)
local function rounds_kind(buf)
  if buf == R_ORIG then return 'orig' end
  if buf == R_MOD then return 'mod4' end
  if buf == R_MOD20 then return 'mod20' end
  if buf == R_TGT then return 'tgt' end
  return nil
end

local DEP_ORIG = unhex(DEP_ORIG_HEX)
-- 模板 = 用目标值替换 +0(字节1..4) 与 +8(字节9..12)，其余逐字节保留
local DEP_MOD  = D_EDITS[1].tgt .. DEP_ORIG:sub(5, 8)
                  .. D_EDITS[2].tgt .. DEP_ORIG:sub(13)
assert(#DEP_ORIG == RECORD_SIZE and #DEP_MOD == RECORD_SIZE,
       'template size ' .. #DEP_ORIG .. '/' .. #DEP_MOD)

-- ------------------------------------------------------------------ ffi
local function setup_ffi()
  local tm = rawget(_G, '__AC8_TEST_MEM')
  if type(tm) == 'table' and type(tm.read) == 'function' then
    api = tm
    return true
  end
  local ok, err = pcall(function()
    local ffi = require('ffi')
    assert(ffi.abi('64bit'), 'windows_x64_required')
    local okc = pcall(ffi.cdef, [[
      typedef struct {
        uintptr_t BaseAddress; uintptr_t AllocationBase;
        uint32_t AllocationProtect; uint32_t PartitionId;
        size_t RegionSize; uint32_t State; uint32_t Protect; uint32_t Type;
      } AC8EV_MBI_V5;
      void  *GetModuleHandleA(const char *);
      uint32_t GetModuleFileNameW(void *, uint16_t *, uint32_t);
      void  *GetCurrentProcess(void);
      int    ReadProcessMemory(void *p, const void *a, void *b, size_t n, size_t *r);
      size_t VirtualQuery(const void *a, AC8EV_MBI_V5 *i, size_t n);
      int    VirtualProtect(void *a, size_t n, uint32_t p, uint32_t *o);
      int    WriteProcessMemory(void *p, void *a, const void *b, size_t n, size_t *r);
      void  *CreateFileW(const uint16_t *, uint32_t, uint32_t, void *, uint32_t, uint32_t, void *);
      int    ReadFile(void *, void *, uint32_t, uint32_t *, void *);
      int    CloseHandle(void *);
      int32_t BCryptOpenAlgorithmProvider(void **, const uint16_t *, const uint16_t *, uint32_t);
      int32_t BCryptCreateHash(void *, void **, void *, uint32_t, const void *, uint32_t, uint32_t);
      int32_t BCryptHashData(void *, const void *, uint32_t, uint32_t);
      int32_t BCryptFinishHash(void *, void *, uint32_t);
      int32_t BCryptDestroyHash(void *);
      int32_t BCryptCloseAlgorithmProvider(void *, uint32_t);
    ]])
    if not okc then error('cdef failed') end
    local k, b = ffi.load('kernel32'), ffi.load('bcrypt')
    local proc = k.GetCurrentProcess()
    local a = {}

    function a.read(address, size)
      if type(address) ~= 'number' or address < 65536
         or address + size >= 0x800000000000 or size <= 0 or size > 8 * 1024 * 1024 then
        return nil
      end
      local buf, cnt = ffi.new('uint8_t[?]', size), ffi.new('size_t[1]')
      if k.ReadProcessMemory(proc, ffi.cast('const void *', address), buf, size, cnt) == 0 then
        return nil
      end
      if tonumber(cnt[0]) ~= size then return nil end
      return ffi.string(buf, size)
    end

    function a.write(address, bytes)
      if type(address) ~= 'number' or type(bytes) ~= 'string' or #bytes < 1 then
        return false
      end
      local info = ffi.new('AC8EV_MBI_V5[1]')
      if k.VirtualQuery(ffi.cast('const void *', address), info, ffi.sizeof(info))
         ~= ffi.sizeof(info) then return false end
      local prot = tonumber(info[0].Protect)
      local base = tonumber(ffi.cast('uintptr_t', info[0].BaseAddress))
      local rsize = tonumber(info[0].RegionSize)
      if tonumber(info[0].State) ~= 0x1000 then return false end
      if not base or address < base or address + #bytes > base + rsize then return false end
      if prot ~= 0x02 and prot ~= 0x04 then return false end
      local old = ffi.new('uint32_t[1]')
      local changed = false
      if prot == 0x02 then
        if k.VirtualProtect(ffi.cast('void *', address), #bytes, 0x04, old) == 0 then
          return false
        end
        changed = true
      end
      local got = ffi.new('size_t[1]')
      local success, result = pcall(function()
        if changed and tonumber(old[0]) ~= prot then return false end
        local ok1 = k.WriteProcessMemory(proc, ffi.cast('void *', address),
                                         bytes, #bytes, got) ~= 0
        return ok1 and tonumber(got[0]) == #bytes
      end)
      if changed then
        k.VirtualProtect(ffi.cast('void *', address), #bytes, old[0], old)
      end
      return success and result
    end

    function a.raw_region_at(address)
      if type(address) ~= 'number' or address < 0
         or address >= 0x7FFFFFFFFFFF then return nil end
      local info = ffi.new('AC8EV_MBI_V5[1]')
      if k.VirtualQuery(ffi.cast('const void *', address), info, ffi.sizeof(info)) == 0 then
        return nil
      end
      local base = tonumber(info[0].BaseAddress)
      local size = tonumber(info[0].RegionSize)
      if not base or not size or size <= 0 then return nil end
      return {
        base = base, size = size,
        state = tonumber(info[0].State),
        protect = tonumber(info[0].Protect),
        mtype = tonumber(info[0].Type),
      }
    end

    function a.module(name)
      local h = k.GetModuleHandleA(name)
      if h == nil then return nil end
      return tonumber(ffi.cast('uintptr_t', h))
    end

    function a.module_hash(address)
      local path = ffi.new('uint16_t[32768]')
      local n = k.GetModuleFileNameW(ffi.cast('void *', address), path, 32768)
      if n == 0 or n >= 32768 then return nil end
      local f = k.CreateFileW(path, 0x80000000, 7, nil, 3, 0x08000000, nil)
      if f == ffi.cast('void *', -1) then return nil end
      local algo, hash = ffi.new('void *[1]'), ffi.new('void *[1]')
      local ok2, digest = pcall(function()
        local nm = ffi.new('uint16_t[7]', { 83, 72, 65, 50, 53, 54, 0 })
        assert(b.BCryptOpenAlgorithmProvider(algo, nm, nil, 0) == 0)
        assert(b.BCryptCreateHash(algo[0], hash, nil, 0, nil, 0, 0) == 0)
        local chunk, cnt = ffi.new('uint8_t[65536]'), ffi.new('uint32_t[1]')
        local total = 0
        while true do
          assert(k.ReadFile(f, chunk, 65536, cnt, nil) ~= 0)
          if cnt[0] == 0 then break end
          total = total + tonumber(cnt[0])
          assert(total <= 64 * 1024 * 1024)
          assert(b.BCryptHashData(hash[0], chunk, cnt[0], 0) == 0)
        end
        local d = ffi.new('uint8_t[32]')
        assert(b.BCryptFinishHash(hash[0], d, 32, 0) == 0)
        local parts = {}
        for i = 0, 31 do parts[#parts + 1] = string.format('%02x', d[i]) end
        return table.concat(parts)
      end)
      if hash[0] ~= nil then b.BCryptDestroyHash(hash[0]) end
      if algo[0] ~= nil then b.BCryptCloseAlgorithmProvider(algo[0], 0) end
      k.CloseHandle(f)
      if not ok2 then return nil end
      return digest
    end

    api = a
  end)
  if not ok then
    M.phase = 'failed'
    M.fail_reason = 'ffi: ' .. tostring(err)
    add(M.fail_reason)
    flush_all()
  end
  return ok
end

-- 统一的枚举状态重置（gaps 残留会让下一轮枚举在开头就误判结束——踩过）
local function reset_enum()
  M.em = nil
  M.dep_addr = nil
  M.rounds_addr = nil
  M.rounds_checked = false
  M.enum_addr = 0x10000
  M.enum_done = false
  M.enum_count = 0
  M.gaps = 0
  M.cand = {}
  M.head_i = 1
  M.scan_cursor = 0
  M.scan_done = false
end

-- ------------------------------------------------------------------ 枚举（分帧）
local function enum_slice()
  local deadline = os.clock() + BUDGET
  local n = 0
  while n < ENUM_PER_SLICE do
    local addr = M.enum_addr
    if not addr or addr >= 0x7FFFFFFFFFFF then
      M.enum_done = true
      return true
    end
    local r = api.raw_region_at(addr)
    if not r then
      M.gaps = M.gaps + 1
      if M.gaps > 512 then
        M.enum_done = true
        return true
      end
      M.enum_addr = addr + 65536
    else
      M.gaps = 0
      if r.size <= 0 or r.base + r.size <= addr then
        M.enum_done = true
        return true
      end
      M.enum_addr = r.base + r.size
      M.enum_count = M.enum_count + 1
      if r.state == 0x1000 and r.mtype == 0x20000
         and r.size >= CAND_MIN_SIZE and r.size <= CAND_MAX_SIZE then
        M.cand[#M.cand + 1] = { base = r.base, size = r.size }
      end
    end
    n = n + 1
    if os.clock() > deadline then return false end
  end
  return false
end

-- ------------------------------------------------------------------ 头部校验（分帧）
local function head_slice()
  local deadline = os.clock() + BUDGET
  local want = unhex(PB_MAP_HEADER)
  local n = 0
  while M.head_i <= #M.cand and n < 32 do
    local c = M.cand[M.head_i]
    M.head_i = M.head_i + 1
    n = n + 1
    local h = api.read(c.base, 28)
    if h and #h == 28 and h == want then
      M.em = c.base
      M.em_size = c.size
      add(('EntityManager 锚定 @0x%X  size=%d%s'):format(
        c.base, c.size,
        c.size == PB_EM_SIZE_HINT and '（=profile 常量）'
          or ('（profile 常量 46616576，差 ' .. tostring(c.size - PB_EM_SIZE_HINT) .. '）')))
      flush_all()
      return true
    end
    if os.clock() > deadline then return false end
  end
  return M.head_i > #M.cand
end

-- ------------------------------------------------------------------ 表定位
local function table_primary_ok()
  local h = api.read(M.em + M.dep_off, 28)
  if not h or #h < 28 then return false end
  if h == unhex('4c444c440100000085ba35c47015000001000000000000007ab66991') then
    M.dep_addr = M.em + M.dep_off
    M.dep_off_src = 'fixed'
    return true
  end
  -- 前 12 字节（LDLD+ver+dlsum）吻合就认（尾部字段可能随内容漂移）
  if h:sub(1, 12) == 'LDLD' .. string.char(1, 0, 0, 0) .. DEP_HASH_LE then
    M.dep_addr = M.em + M.dep_off
    M.dep_off_src = 'fixed_head12'
    add(('Deposit 表头前 12 字节吻合、后 16 字节漂移，仍采用（%s）'):format(hex(h)))
    return true
  end
  return false
end

local function table_fallback_slice()
  local deadline = os.clock() + BUDGET
  local pattern = 'LDLD' .. string.char(1, 0, 0, 0) .. DEP_HASH_LE
  local n = 0
  while n < FALLBACK_PER_SLICE and not M.scan_done do
    local off = M.scan_cursor
    if off >= M.em_size then
      M.scan_done = true
      return false
    end
    local want = FALLBACK_CHUNK
    if off + want > M.em_size then want = M.em_size - off end
    -- 读可能因跨区/跨分配被拒：逐级降级重试，失败则按小步推进
    local b = api.read(M.em + off, want + 16)
        or api.read(M.em + off, math.min(want, 4096))
        or api.read(M.em + off, 512)
    if not b then
      M.scan_cursor = off + 4096
      n = n + 1
      if os.clock() > deadline then return false end
    else
      local i = b:find(pattern, 1, true)
      if i then
        M.dep_addr = M.em + off + i - 1
        M.dep_off = off + i - 1
        M.dep_off_src = 'em_search'
        add(('Deposit 表定位（EM 内搜索）@0x%X  owner+%d'):format(M.dep_addr, M.dep_off))
        flush_all()
        return true
      end
    end
    M.scan_cursor = off + want
    n = n + 1
    if os.clock() > deadline then return false end
  end
  return M.scan_done
end

-- ------------------------------------------------------------------ 单行写入
local function edits_of(kind)
  if kind == 'R' then return R_EDITS end
  return D_EDITS
end

local function apply_row(addr, why, kind)
  local list = edits_of(kind)
  M.written = M.written or {}
  local done = true
  for _, e in ipairs(list) do
    local at = addr + e.off
    local cur = api.read(at, 4)
    -- e.olds：该字段的历史旧值集合（原版值 + 我们历史版本写入的值）。
    -- 没有就退化为单个 e.old。
    local olds = e.olds or { e.old }
    local is_old = false
    for i = 1, #olds do
      if cur == olds[i] then is_old = true end
    end
    if cur == e.tgt then
      M.written[at] = { kind = kind, off = e.off }
      add(('%s 已是目标值：0x%X（%s）'):format(e.label, at, why), true)
    elseif is_old then
      local ok = api.write(at, e.tgt)
      local back = ok and api.read(at, 4)
      if back == e.tgt then
        M.writes = M.writes + 1
        M.written[at] = { kind = kind, off = e.off }
        add(('%s %s @0x%X（%s，回读 OK）'):format(e.label, e.desc, at, why), true)
      else
        M.refusals = M.refusals + 1
        add(('%s 写入失败/回读不符 @0x%X'):format(e.label, at), true)
        done = false
      end
    else
      M.refusals = M.refusals + 1
      add(('%s 既非旧值也非目标值，拒绝 @0x%X cur=%s'):format(e.label, at, hex(cur)), true)
      done = false
    end
  end
  flush_all()
  return done
end

-- 整条已改（幂等）：登记每处编辑地址，看门狗照旧按新旧值复查
local function mark_mod(record, kind)
  M.written = M.written or {}
  for _, e in ipairs(edits_of(kind)) do
    M.written[record + e.off] = { kind = kind, off = e.off, mod = true }
  end
end

-- ------------------------------------------------------------------ Deposit 记录
local function locate_deposit()
  local hdr = api.read(M.dep_addr, 28)
  if not hdr or #hdr < 16 then
    return false, 'dep_header_unreadable'
  end
  local body_size = u32(hdr, 12) or 0
  if body_size < 512 or body_size > 4 * 1024 * 1024 then
    add(('Deposit 表 size 异常：%s'):format(tostring(body_size)))
    return false, 'dep_size_bad'
  end
  local total = body_size + RECORD_SIZE
  local buf = api.read(M.dep_addr, total)
  if not buf then
    buf = api.read(M.dep_addr, body_size)
    total = buf and #buf or 0
  end
  if not buf or total < RECORD_SIZE then
    return false, 'dep_body_unreadable'
  end

  local hits, mid_hits = {}, {}
  local from = 1
  while true do
    local i = buf:find(DEP_ORIG, from, true)
    if not i then break end
    hits[#hits + 1] = { addr = M.dep_addr + i - 1, kind = 'orig' }
    from = i + 1
  end
  if #hits == 0 then
    from = 1
    while true do
      local i = buf:find(DEP_MOD, from, true)
      if not i then break end
      hits[#hits + 1] = { addr = M.dep_addr + i - 1, kind = 'mod' }
      from = i + 1
    end
  end
  if #hits == 0 then
    from = 1
    while true do
      local i = buf:find(DEP_MARK, from, true)
      if not i then break end
      if i >= 13 then
        mid_hits[#mid_hits + 1] = M.dep_addr + i - 1 - 12
      end
      from = i + 1
    end
  end

  M.written = M.written or {}
  if #hits == 0 and #mid_hits == 0 then
    add(('Deposit 表（%d 字节）内无目标记录 —— 模板变了，拒绝写入'):format(total), true)
    add('  表头 hex: ' .. hex(hdr), true)
    return false, 'record_not_found'
  end

  local n0 = 0
  for _ in pairs(M.written) do n0 = n0 + 1 end

  for _, h in ipairs(hits) do
    if h.kind == 'mod' then
      mark_mod(h.addr, 'D')
      add(('背包记录已在目标态（历史写入保持中）@0x%X'):format(h.addr), true)
    else
      apply_row(h.addr, '整条 152B 模板匹配', 'D')
    end
  end

  for _, addr in ipairs(mid_hits) do
    local r = api.read(addr, RECORD_SIZE)
    if r and #r == RECORD_SIZE then
      local f0, f8 = r:sub(1, 4), r:sub(9, 12)
      local e0 = (f0 == D_EDITS[1].old or f0 == D_EDITS[1].tgt)
      local e8 = (f8 == D_EDITS[2].old or f8 == D_EDITS[2].tgt)
      if e0 and e8 then
        apply_row(addr, '中段匹配+逐字段判定', 'D')
      else
        M.refusals = M.refusals + 1
        add(('中段命中但字段非法，拒绝 @0x%X  +0=%s +8=%s  行=%s')
              :format(addr, hex(f0), hex(f8), hex(r)), true)
      end
    else
      add(('中段命中但行读不全 @0x%X'):format(addr), true)
    end
  end

  local n = 0
  for _ in pairs(M.written) do n = n + 1 end
  if n == n0 then
    return false, 'no_writable_rows'
  end
  return true
end

-- ------------------------------------------------------------------ Rounds 记录（v6 新增）
-- 表：EM + ROUNDS_OFF（固定偏移，两次探针一致）+ 表头 12 字节 dlsum 校验。
-- 记录：**先按原版配方** table + 800(#hashmap) + 23*136，内容三态校验；
--       不符则表体单次读全模板搜索；再不符 → dump 配方位，拒绝（绝不盲写）。
local function locate_rounds()
  if not M.rounds_addr then
    add('rounds 表未定位，跳过弹仓编辑（背包侧不受影响）')
    return false, 'rounds_table_missing'
  end
  local head = api.read(M.rounds_addr, 28)
  if not head or #head < 12 then
    return false, 'rounds_header_unreadable'
  end
  if head:sub(1, 12) ~= 'LDLD' .. string.char(1, 0, 0, 0) .. ROUNDS_HASH_LE then
    add('rounds 表头 dlsum 不符，拒绝弹仓编辑；表头=' .. hex(head), true)
    return false, 'rounds_header_mismatch'
  end

  local recipe = M.rounds_addr + ROUNDS_MAPLEN + ROUNDS_INDEX * ROUNDS_SIZE
  local rec, where
  local b = api.read(recipe, ROUNDS_SIZE)
  if b and #b == ROUNDS_SIZE then
    local k = rounds_kind(b)
    if k then rec, where = recipe, 'recipe_' .. k end
  end
  if not where then
    -- 表体兜底：三种已知模板之一（原版 / 6.0.0 态 / 6.1.0 目标态）
    local body_size = u32(head, 12) or ROUNDS_MAPLEN
    local body = api.read(M.rounds_addr, math.min(body_size, 4 * 1024 * 1024) + ROUNDS_SIZE)
    if body then
      for _, pat in ipairs({ { R_ORIG, 'search_orig' }, { R_MOD, 'search_mod4' },
                             { R_MOD20, 'search_mod20' }, { R_TGT, 'search_tgt' } }) do
        if not where then
          local i = body:find(pat[1], 1, true)
          if i then rec, where = M.rounds_addr + i - 1, pat[2] end
        end
      end
    end
  end
  if not where then
    add(('rounds 记录既不在配方位 0x%X 也没匹配三种已知模板 —— 拒绝弹仓编辑；配方位前 32 字节:')
          :format(recipe), true)
    local dbg = api.read(recipe, 32)
    if dbg then add('  ' .. hex(dbg), true) end
    flush_all()
    return false, 'rounds_record_not_found'
  end
  if where:find('_tgt') then
    mark_mod(rec, 'R')
    add(('弹仓记录已是目标态 @0x%X，定位=%s'):format(rec, where), true)
    return true
  end
  -- orig / mod4 / search_* 都交给 apply_row 逐字段判定：
  -- 72 只认 10.0f->20.0f；96 认 {6.0f,4.0f}->20.0f —— 部分已改的行会被补齐
  apply_row(rec, '136B 模板匹配（' .. where .. '）', 'R')
  local nr = 0
  for _, e in ipairs(R_EDITS) do
    if M.written[rec + e.off] then nr = nr + 1 end
  end
  return nr > 0, (nr > 0 and nil or 'rounds_write_refused')
end

-- ------------------------------------------------------------------ 看门狗
local function find_edit(kind, off)
  for _, e in ipairs(edits_of(kind)) do
    if e.off == off then return e end
  end
  return nil
end

local function recheck()
  M.checks = M.checks + 1
  if not M.written or not next(M.written) then return end
  local lost = 0
  local addrs = {}
  for at in pairs(M.written) do addrs[#addrs + 1] = at end
  for _, at in ipairs(addrs) do
    local bound = M.written[at]
    local cur = api.read(at, 4)
    if cur == nil then
      M.written[at] = nil
      lost = lost + 1
    else
      local e = type(bound) == 'table' and find_edit(bound.kind, bound.off or -1) or nil
      if e then
        if cur == e.tgt then
          -- 保持
        elseif (function()
          local olds = e.olds or { e.old }
          for i = 1, #olds do
            if cur == olds[i] then return true end
          end
          return false
        end)() then
          if api.write(at, e.tgt) and api.read(at, 4) == e.tgt then
            M.writes = M.writes + 1
            add(('看门狗重写成功 %s @0x%X'):format(e.label, at), true)
          else
            add(('看门狗重写失败 @0x%X'):format(at), true)
            M.written[at] = nil
            lost = lost + 1
          end
        else
          add(('看门狗：%s 值异常 %s @0x%X（丢弃）'):format(
            e.label, hex(cur), at), true)
          M.written[at] = nil
          lost = lost + 1
        end
      else
        M.written[at] = nil
        lost = lost + 1
      end
    end
  end
  -- 表头复验：任一表消失（EM 卸载/重载）→ 重新定位
  local heads = { { key = 'Deposit', addr = M.dep_addr },
                  { key = 'rounds', addr = M.rounds_addr } }
  for _, h in ipairs(heads) do
    if h.addr then
      local b = api.read(h.addr, 12)
      local ok = b and b:sub(1, 4) == 'LDLD'
      if not ok then
        add(h.key .. ' 表头复验失败（EM 卸载/重载），重新定位', true)
        reset_enum()
        M.phase = 'enum'
        M.rounds = M.rounds + 1
        flush_all()
        return
      end
    end
  end
  local n = 0
  for _ in pairs(M.written) do n = n + 1 end
  if n == 0 and lost > 0 then
    add('所有已写地址失效，重新定位', true)
    reset_enum()
    M.phase = 'enum'
    M.rounds = M.rounds + 1
    flush_all()
  end
end

-- ------------------------------------------------------------------ 退避
local function enter_wait(reason)
  M.waits = M.waits + 1
  local secs
  if M.waits <= MAX_BACKOFF_N then
    secs = BACKOFF[M.waits]
  else
    secs = 60
  end
  M.phase = 'wait'
  M.due_frame = M.frame + secs * 60
  reset_enum()
  add(('第 %d 轮失败：%s；%d 秒后重试（EM/表通常进任务后才加载）')
        :format(M.waits, tostring(reason), secs), true)
  flush_all()
end

-- ------------------------------------------------------------------ 每帧
local function step()
  M.frame = M.frame + 1

  if not M.armed then
    if M.frame < ARM_FRAME then return end
    M.armed = true
    add('armed：第 ' .. M.frame .. ' 帧，初始化 ffi')
    if not setup_ffi() then return end
    M.game = nil
    pcall(function() M.game = api.module('game.dll') end)
    if not M.game then
      pcall(function() M.game = api.module('Game.dll') end)
    end
    M.phase = 'lock'
    return
  end

  if M.phase == 'failed' then
    if M.frame % 600 == 0 then flush_all() end
    return
  end

  local steady = (M.phase == 'patched')
  local cadence = steady and STEADY_CADENCE or SCAN_CADENCE
  if (M.frame % cadence) ~= 0 then return end

  if M.phase == 'lock' then
    local h = nil
    if api.module_hash and M.game then
      pcall(function() h = api.module_hash(M.game) end)
    end
    if h then
      if h ~= MODULE_SHA256 then
        M.phase = 'failed'
        M.fail_reason = 'unsupported_game_dll_no_write got=' .. h
        add(M.fail_reason, true)
        flush_all()
        return
      end
      add('game.dll 哈希校验通过')
    else
      add('game.dll 哈希不可读，跳过构建锁（已记录）')
    end
    M.rounds = M.rounds + 1
    M.phase = 'enum'
    add(('=== 第 %d 轮定位开始 ==='):format(M.rounds))
    flush_all()
    return
  end

  if M.phase == 'enum' then
    local ok, err = pcall(enum_slice)
    if not ok then
      M.errs = M.errs + 1
      add('枚举异常(已吞): ' .. tostring(err))
      flush_all()
      if M.errs >= 3 then
        M.phase = 'failed'
        M.fail_reason = 'enum_error: ' .. tostring(err)
        flush_all()
      end
      return
    end
    if M.enum_done then
      add(('区域枚举完成：%d 个区域，%d 个尺寸候选')
            :format(M.enum_count, #M.cand))
      M.head_i = 1
      M.phase = 'head'
      flush_all()
    end
    return
  end

  if M.phase == 'head' then
    local ok, all_done = pcall(head_slice)
    if not ok then
      M.errs = M.errs + 1
      add('头部校验异常(已吞): ' .. tostring(all_done))
      flush_all()
      return
    end
    if M.em then
      M.phase = 'table'
      return
    end
    if all_done then
      enter_wait(('EM 未出现（%d 个候选头不匹配）'):format(#M.cand))
      return
    end
    return
  end

  if M.phase == 'table' then
    if table_primary_ok() then
      add(('Deposit 表 @0x%X（固定偏移 EM+%d，来源 %s）')
            :format(M.dep_addr, M.dep_off, M.dep_off_src))
      M.phase = 'locate'
      flush_all()
      return
    end
    add(('固定偏移表头不匹配，EM 内按 LDLD+dlsum 搜索（%d MB，切片）')
          :format(math.floor((M.em_size or 0) / 1048576)))
    M.scan_cursor = 0
    M.scan_done = false
    M.phase = 'tfall'
    flush_all()
    return
  end

  if M.phase == 'tfall' then
    local ok, found = pcall(table_fallback_slice)
    if not ok then
      M.errs = M.errs + 1
      add('表回退搜索异常(已吞): ' .. tostring(found))
      enter_wait('table_fallback_error')
      return
    end
    if M.dep_addr then
      M.phase = 'locate'
      return
    end
    if M.scan_done then
      enter_wait('deposit_table_not_found_in_em')
      return
    end
    return
  end

  if M.phase == 'locate' then
    -- rounds 表定位（v6）：只做一次，两条路径（primary/tfall）都会经过这里
    if not M.rounds_addr and not M.rounds_checked then
      M.rounds_checked = true
      local rh = api.read(M.em + ROUNDS_OFF, 28)
      if rh and rh:sub(1, 12) == 'LDLD' .. string.char(1, 0, 0, 0) .. ROUNDS_HASH_LE then
        M.rounds_addr = M.em + ROUNDS_OFF
        add(('rounds 表 @0x%X（固定偏移 EM+%d，头校验通过）')
              :format(M.rounds_addr, ROUNDS_OFF))
      else
        add('rounds 表头不符，弹仓编辑将跳过；表头=' .. (rh and hex(rh) or '不可读'))
      end
    end
    -- 先背包（v5 已验证），再弹仓+阈值（v6 新增）；两者独立、各自报告
    local okD, resD, whyD = pcall(locate_deposit)
    if not okD then
      M.errs = M.errs + 1
      add('背包记录定位异常(已吞): ' .. tostring(resD))
      enter_wait('dep_locate_error')
      return
    end
    local okR, resR, whyR = pcall(locate_rounds)
    if not okR then
      M.errs = M.errs + 1
      add('弹仓记录定位异常(已吞): ' .. tostring(resR))
      resR, whyR = false, 'rounds_locate_error'
    end
    local n = 0
    if M.written then for _ in pairs(M.written) do n = n + 1 end end
    if resD then
      if not resR then
        add(('注意：弹仓侧未完成（%s）；背包侧已生效'):format(tostring(whyR)), true)
      end
      M.phase = 'patched'
      M.waits = 0
      add(('=== 补丁生效：%d 处地址（背包%s / 弹仓%s），进入看门狗（每 %.0f 秒复核）===')
            :format(n, resD and 'OK' or 'X', resR and 'OK' or 'X',
                   RECHECK_EVERY / 60), true)
      flush_all()
    else
      enter_wait(tostring(whyD) or 'locate_failed')
    end
    return
  end


  if M.phase == 'wait' then
    if M.frame >= M.due_frame then
      M.rounds = M.rounds + 1
      M.phase = 'lock'
      add(('=== 第 %d 轮定位开始 ==='):format(M.rounds))
      flush_all()
    end
    return
  end
end

-- ------------------------------------------------------------------ 挂帧
do
  local previous_update = rawget(_G, 'update')
  if type(previous_update) == 'function' then
    update = function(...)
      local ok2, err = pcall(step)
      if not ok2 then
        M.errs = (M.errs or 0) + 1
        if M.errs <= 3 then pcall(add, 'step 出错(已吞): ' .. tostring(err)) end
      end
      return previous_update(...)
    end
    M.hooked = true
    add('已挂钩子；第 ' .. ARM_FRAME .. ' 帧之前不做任何重活')
  else
    M.phase = 'failed'
    M.fail_reason = 'update_not_function'
    add('加载期 update 不是函数，未挂钩子。')
  end
end

flush_all()
return M

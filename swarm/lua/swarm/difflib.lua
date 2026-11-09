-- Python's difflib.SequenceMatcher(None, a, b, autojunk=False), ported faithfully: the conflict tests depend on
-- its exact opcodes. a and b are Lua arrays; every index here is Python's (0-based, half-open spans).
local M = {}

local SM = {}
SM.__index = SM

function M.SequenceMatcher(a, b)
  local b2j = {}  -- no junk, and no popular elements without autojunk
  for j = 1, #b do
    local l = b2j[b[j]]
    if not l then l = {}; b2j[b[j]] = l end
    l[#l + 1] = j - 1
  end
  return setmetatable({ a = a, b = b, b2j = b2j }, SM)
end

-- The longest matching block in a[alo:ahi] and b[blo:bhi]: the earliest in a, then in b, on ties.
function SM:find_longest_match(alo, ahi, blo, bhi)
  local a, b, b2j = self.a, self.b, self.b2j
  local besti, bestj, bestsize = alo, blo, 0
  local j2len = {}
  for i = alo, ahi - 1 do
    local newj2len = {}
    for _, j in ipairs(b2j[a[i + 1]] or {}) do
      if j >= blo then
        if j >= bhi then break end
        local k = (j2len[j - 1] or 0) + 1
        newj2len[j] = k
        if k > bestsize then besti, bestj, bestsize = i - k + 1, j - k + 1, k end
      end
    end
    j2len = newj2len
  end
  -- Python's extension over non-junk neighbours (a no-op without junk, kept as written)
  while besti > alo and bestj > blo and a[besti] == b[bestj] do
    besti, bestj, bestsize = besti - 1, bestj - 1, bestsize + 1
  end
  while besti + bestsize < ahi and bestj + bestsize < bhi and a[besti + bestsize + 1] == b[bestj + bestsize + 1] do
    bestsize = bestsize + 1
  end
  return besti, bestj, bestsize
end

function SM:get_matching_blocks()
  local la, lb = #self.a, #self.b
  local queue, blocks = { { 0, la, 0, lb } }, {}
  while #queue > 0 do
    local alo, ahi, blo, bhi = unpack(table.remove(queue))
    local i, j, k = self:find_longest_match(alo, ahi, blo, bhi)
    if k > 0 then
      blocks[#blocks + 1] = { i, j, k }
      if alo < i and blo < j then queue[#queue + 1] = { alo, i, blo, j } end
      if i + k < ahi and j + k < bhi then queue[#queue + 1] = { i + k, ahi, j + k, bhi } end
    end
  end
  table.sort(blocks, function(x, y) return x[1] < y[1] end)  -- blocks never share an i: no ties
  local i1, j1, k1, out = 0, 0, 0, {}
  for _, x in ipairs(blocks) do
    local i2, j2, k2 = x[1], x[2], x[3]
    if i1 + k1 == i2 and j1 + k1 == j2 then
      k1 = k1 + k2
    else
      if k1 > 0 then out[#out + 1] = { i1, j1, k1 } end
      i1, j1, k1 = i2, j2, k2
    end
  end
  if k1 > 0 then out[#out + 1] = { i1, j1, k1 } end
  out[#out + 1] = { la, lb, 0 }
  return out
end

-- {tag, i1, i2, j1, j2} rows, tag one of replace, delete, insert, equal.
function SM:get_opcodes()
  local i, j, res = 0, 0, {}
  for _, m in ipairs(self:get_matching_blocks()) do
    local ai, bj, size = m[1], m[2], m[3]
    local tag = (i < ai and j < bj) and "replace" or i < ai and "delete" or j < bj and "insert" or nil
    if tag then res[#res + 1] = { tag, i, ai, j, bj } end
    i, j = ai + size, bj + size
    if size > 0 then res[#res + 1] = { "equal", ai, i, bj, j } end
  end
  return res
end

return M

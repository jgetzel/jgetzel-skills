-- The kind of script lua-lean is for: word frequencies of stdin, the most frequent first. luajit wordfreq.lua [top]
local M = {}

function M.count(text)
  local n = {}
  for w in text:lower():gmatch("[%a']+") do n[w] = (n[w] or 0) + 1 end
  return n
end

function M.ranked(n)
  local r = {}
  for w, k in pairs(n) do r[#r + 1] = {word = w, n = k} end
  table.sort(r, function(a, b) if a.n ~= b.n then return a.n > b.n end return a.word < b.word end)
  return r
end

if arg and arg[0] and arg[0]:match("wordfreq%.lua$") then
  local top = tonumber(arg[1]) or 10
  for i, e in ipairs(M.ranked(M.count(io.read("*a")))) do
    if i > top then break end
    io.write(("%6d %s\n"):format(e.n, e.word))
  end
end

return M

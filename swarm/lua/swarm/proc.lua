-- Subprocesses on fork/exec: exec (stdout, stderr, code), run (Python's run: stdout or nil), git, gx.
local unistd, wait, poll = require "posix.unistd", require "posix.sys.wait", require "posix.poll"
local stdlib, fcntl = require "posix.stdlib", require "posix.fcntl"
local util = require "swarm.util"
local M = {}
local signal = require "posix.signal"
signal.signal(signal.SIGPIPE, signal.SIG_IGN)  -- Python's default: a closed pipe is EPIPE, not death

-- Run argv; opts: cwd, input (else stdin is inherited, as subprocess.run), env (set on top of ours, false unsets),
-- merge (stderr into stdout), stdout_file (a path both go to). Returns stdout, stderr, exit code (127: no binary,
-- -N: killed by signal N).
function M.exec(argv, o)
  o = o or {}
  local ir, iw
  if o.input then ir, iw = unistd.pipe() end
  local or_, ow = unistd.pipe()
  local er, ew = unistd.pipe()
  local pid = unistd.fork()
  if pid == 0 then
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)  -- an ignored signal survives exec; subprocess restores it too
    if ir then unistd.dup2(ir, 0) end
    local out = ow
    if o.stdout_file then
      out = fcntl.open(o.stdout_file, fcntl.O_WRONLY + fcntl.O_CREAT + fcntl.O_TRUNC, 420) or unistd._exit(127)
    end
    unistd.dup2(out, 1)
    unistd.dup2((o.merge or o.stdout_file) and out or ew, 2)
    for _, f in ipairs({ ir, iw, or_, ow, er, ew }) do unistd.close(f) end
    if o.cwd and not unistd.chdir(o.cwd) then unistd._exit(127) end
    for k, v in pairs(o.env or {}) do stdlib.setenv(k, v or nil) end
    unistd.execp(argv[1], { select(2, unpack(argv)) })
    unistd._exit(127)
  end
  if ir then unistd.close(ir) end
  unistd.close(ow); unistd.close(ew)
  local out, err, s, i = {}, {}, o.input, 1
  local fds = { [or_] = { events = { IN = true } }, [er] = { events = { IN = true } } }
  if iw then fds[iw] = { events = { OUT = true } } end
  while next(fds) do  -- input is written as the child reads it, so neither side blocks on a full pipe
    poll.poll(fds, -1)
    for fd, f in pairs(fds) do
      local ev = f.revents or {}
      if fd == iw and (ev.OUT or ev.ERR or ev.HUP) then
        local n = ev.OUT and i <= #s and unistd.write(iw, s:sub(i, i + 4095))  -- PIPE_BUF: POLLOUT promises room for that much
        i = i + (n or #s + 1)  -- a child that closed its stdin (EPIPE) gets no more
        if i > #s then unistd.close(iw); fds[iw] = nil end
      elseif fd ~= iw and (ev.IN or ev.HUP or ev.ERR) then
        local r = unistd.read(fd, 65536)
        if not r or #r == 0 then
          unistd.close(fd); fds[fd] = nil
        else
          table.insert(fd == or_ and out or err, r)
        end
      end
    end
  end
  local _, how, code = wait.wait(pid)
  return table.concat(out), table.concat(err), how == "exited" and code or -code
end

function M.run(argv, cwd, input, env)
  local out, _, code = M.exec(argv, { cwd = cwd, input = input, env = env })
  if code == 0 then return out end
  return nil
end

function M.git(args, cwd)
  local out = M.run({ "git", unpack(args) }, cwd)
  return out and util.strip(out) or nil
end

-- (returncode, stderr) of a git command.
function M.gx(args, cwd)
  local _, err, code = M.exec({ "git", unpack(args) }, { cwd = cwd })
  return code, util.strip(err)
end

return M

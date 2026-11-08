import importlib.util, os, sqlite3, unittest
spec = importlib.util.spec_from_file_location("sr", os.path.join(os.path.dirname(__file__), "swarm-report.py"))
sr = importlib.util.module_from_spec(spec); spec.loader.exec_module(sr)

class T(unittest.TestCase):
  def test_claim_to_done(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into task values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x'),(160,'a','digest',null);""")
    r = sr.report(c, git=False)
    self.assertEqual(r["tasks"][0]["took"], "1m30s"); self.assertEqual(r["friction"][0]["kind"], "reap"); self.assertEqual(len(r["idle_with_open_tasks"]), 1)

if __name__ == '__main__':
    unittest.main()

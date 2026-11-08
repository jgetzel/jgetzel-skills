import importlib.util, os, sqlite3, sys
spec = importlib.util.spec_from_file_location("sr", os.path.join(os.path.dirname(__file__), "swarm-report.py"))
sr = importlib.util.module_from_spec(spec); spec.loader.exec_module(sr)
sys.path.insert(0, "../swarm")

def test_claim_to_done():
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into task values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x');""")
    r = sr.report(c)
    assert r["tasks"][0]["took"] == "1m30s" and r["friction"][0]["kind"] == "reap"

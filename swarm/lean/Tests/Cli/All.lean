import Tests.Cli.Away
import Tests.Cli.Bases
import Tests.Cli.Comms
import Tests.Cli.Core
import Tests.Cli.Herdr
import Tests.Cli.Lifecycle
import Tests.Cli.Panel
import Tests.Cli.Queue
import Tests.Cli.Scale
import Tests.Cli.Spawn
import Tests.Cli.Stay
import Tests.Cli.Stop
import Tests.Cli.WatchdRun
import Tests.Spec.Cost
import Tests.Spec.Db
import Tests.Spec.Env
import Tests.Spec.Report
import Tests.Spec.Foundation
import Tests.Spec.Sqlite
import Tests.Spec.Watchd

/-! Every spec of swarm-tests, by the Lua spec file it ports. -/

namespace SwarmLean.Tests.Cli

/-- (spec, its tests). -/
def specs : List (String × List Case) := [
  ("cli_away_spec", Away.tests),
  ("cli_bases_spec", Bases.tests),
  ("cli_comms_spec", Comms.tests),
  ("cli_core_spec", Core.tests),
  ("herdr_mods_spec", Herdr.tests),
  ("cli_lifecycle_spec", Lifecycle.tests),
  ("cli_panel_spec", Panel.tests),
  ("cli_queue_spec", Queue.tests),
  ("cli_scale_spec", Scale.tests),
  ("cli_spawn_spec", Spawn.tests),
  ("cli_stay_spec", Stay.tests),
  ("cli_stop_spec", Stop.tests),
  ("cli_watchd_run_spec", WatchdRun.tests),
  ("cost_spec", Spec.Cost.tests),
  ("db_spec", Spec.Db.tests),
  ("env_spec", Spec.Env.tests),
  ("foundation_spec", Spec.Foundation.tests),
  ("sqlite_spec", Spec.Sqlite.tests),
  ("swarm_report_spec", Spec.Report.tests),
  ("watchd_spec", Spec.Watchd.tests)]

end SwarmLean.Tests.Cli

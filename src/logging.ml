open Logger

let _ = Logger.init [("Prover", WARN); ("Main", INFO)] dbg_formatter


let main_log = make_log "Main"
let prover_log = make_log "Prover"

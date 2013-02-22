open Logger

let _ = Logger.init [("Prover", WARN); ("Main", DEBUG); ("SmtLib", DEBUG)] dbg_formatter


let main_log = make_log "Main"
let prover_log = make_log "Prover"
let smtlib_log = make_log "SmtLib"

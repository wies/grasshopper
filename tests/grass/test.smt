(set-option :print-success false)
(set-option :produce-models true)
(set-option :mbqi true)
(set-logic UF)
(declare-sort Loc 0)
(declare-sort Set 1)
(declare-sort Fld 1)
(declare-fun read ((Fld Loc) Loc) Loc)
(declare-fun write ((Fld Loc) Loc Loc) (Fld Loc))
(declare-fun ReachWO ((Fld Loc) Loc Loc Loc) Bool)
(declare-fun f () (Fld Loc))
(declare-fun g () (Fld Loc))
(declare-fun x () Loc)
(declare-fun y () Loc)
(declare-fun z () Loc)

(assert (!(= (write f x y) g) :named _1))

(assert (!(= (read f z) x) :named _2))

(assert (!(ReachWO f x y z) :named _3))

(check-sat)
(exit)

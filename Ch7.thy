theory Ch7
  imports Big_Step
begin

(*
datatype com =
    SKIP 
  | Assign vname aexp    ("_ ::= _" [1000, 61] 61)
  | Seq    com  com      ("_;;/ _"  [60, 61] 60)
  | If     bexp com com  ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While  bexp com      ("(WHILE _/ DO _)"  [0, 61] 61)
*)

(* 7.1 *)

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (Assign v a) = {v}" |
"assigned (Seq c1 c2) = (assigned c1 \<union> assigned c2)" |
"assigned (If b c1 c2) = (assigned c1 \<union> assigned c2)" |
"assigned (While b c) = assigned c"

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
  apply(induction rule: big_step_induct)
  apply(auto)
  done

(* 7.2 *)



end
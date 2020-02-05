theory Ch4
  imports Main
begin

(* 4.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) = {x} \<union> set l \<union> set r"

value "set (Node Tip (1::nat) (Node (Node Tip 1 Tip) 4 Tip))"

fun cmpt :: "int tree \<Rightarrow> (int \<Rightarrow> bool) \<Rightarrow> bool" where
"cmpt Tip _ = True" |
"cmpt (Node l x r) p = ((cmpt l p) \<and> (cmpt r p) \<and> (p x))"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l x r) = (ord l \<and> ord r \<and> (\<forall>z \<in> set l. z \<le> x) \<and> (\<forall>z \<in> set r. z \<ge> x))"

value "ord Tip"
value "ord (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip))"
value "ord (Node (Node Tip 3 Tip) 2 (Node Tip 3 Tip)) = False"
value "ord (Node (Node Tip 2 Tip) 2 (Node Tip 3 Tip))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l a r) = (if x = a then (Node l a r) else
                       if x < a then (Node (ins x l) a r) else
                                     (Node l a (ins x r)))"

value "ins 0 (ins 3 (Node (Node Tip 1 Tip) 4 (Node Tip 8 Tip)))"
value "ord (ins 0 (ins 3 (Node (Node Tip 1 Tip) 4 (Node Tip 8 Tip))))"

lemma [simp]: "set (ins x t) = {x} \<union> set t"
  apply (induction t)
  apply auto
  done

lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t)
  apply auto
  done

(* аксиома? x > a \<and> \<forall> y \<in> S. x > y \<Longrightarrow> \<forall> z \<in> (S \<union> {x}). z > a *)

(* 4.2 *)

inductive pal :: "'a list \<Rightarrow> bool" where
pE: "pal []" |
pS: "pal [a]" |
pC: "pal xs \<Longrightarrow> pal (a # xs @ [a])"

lemma "pal xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: pal.induct)
  apply(auto)
  done

(* 4.3 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma starflip[simp]: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(rule step)
  apply(simp)
  apply(rule refl)
  apply(simp add: step)
  done

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star'flip[simp]: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(auto intro: step' refl')
(*
  apply(rule step')
  apply(rule refl')
  apply(simp)
  apply(simp add: refl' step')
*)
  done


lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
  apply(auto intro: step refl refl')
  done

(* 4.4 *)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
itern: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
  apply(induction rule: iter.induct)
  apply(auto intro: step refl)
  done

lemma "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply(induction rule: star.induct)
  apply(auto intro: iter0 itern)
  done

(* 4.5 *)

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S0:  "S Nil" |
aSb: "S s \<Longrightarrow> S (a # s @ [b])" |
SS:  "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

inductive T :: "alpha list \<Rightarrow> bool" where
T0:   "T Nil" |
TaTb: "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ a # y @ [b])"

lemma TS: "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
  apply(rule S0)
  apply(rule SS)
  apply(simp)
  apply(rule aSb)
  apply(simp)
  (* apply(auto intro: S0 aSb SS) *)
  done

lemma aTb: "T x \<Longrightarrow> T (a # x @ [b])"
  (* try found it *)
  by (metis Cons_eq_appendI T.simps self_append_conv2)

lemma TT: "T y \<Longrightarrow> T x \<Longrightarrow> T (x @ y)"
  apply(induction rule: T.induct)
  apply(auto intro: TaTb T0)
  by (metis T.simps append_eq_appendI)

lemma ST: "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
  apply(rule T0)
  apply(rule aTb)
  apply(simp)
  apply(rule TT)
  apply(simp)
  apply(simp)
  done

(* 4.6 *)

(* aexp and aval *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x ) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* aval_rel даёт конфликт *)
inductive iaval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
iaN: "iaval (N n) s n" |
iaV: "iaval (V v) s (s v) " |
iaP: "iaval xl s vl \<Longrightarrow> iaval xr s vr \<Longrightarrow> iaval (Plus xl xr) s (vl + vr)"

lemma iaa: "iaval e s v \<Longrightarrow> aval e s = v"
  apply(induction rule: iaval.induct)
  apply(auto intro: iaN iaV iaP)
  done

lemma aia: "aval e s = v \<Longrightarrow> iaval e s v"
  apply(induction e arbitrary: v)
  apply(auto)
  apply(rule iaN)
  apply(rule iaV)
  apply(rule iaP)
  apply(auto)
  done

(* 4.7 *)

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

abbreviation hd2 where 
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 where 
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD x) s stk = Some (s(x) # stk)" |
"exec1 ADD _ stk = 
 (case stk of 
  (x # y # xs) \<Rightarrow> Some ((hd2 stk + hd stk) # tl2 stk) |
  (xs) \<Rightarrow> None)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = 
 (case (exec1 i s stk) of 
  Some res \<Rightarrow> exec is s res |
  None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_0: "ok n [] n" |
ok_LI: "ok n is n' \<Longrightarrow> ok n (is @ [LOADI k]) (Suc n')" |
ok_L: "ok n is n' \<Longrightarrow> ok n (is @ [LOAD x]) (Suc n')" |
ok_A: "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

(* can't use stack instead of instr list? *)
inductive ok2 :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
okNil:   "ok2 n Nil n" |
okLOADI: "ok2 n [LoadI i] (Suc n)" |
okLOAD:  "ok2 n [Load x] (Suc n)" | 
okADD:   "ok2 (Suc (Suc n)) [ADD] (Suc n)" |
okConc:  "ok2 p s1 q \<Longrightarrow> ok2 q s2 r \<Longrightarrow> ok2 p (s1 @ s2) r"

lemma "ok2 n ii n' \<Longrightarrow> length stk = n \<Longrightarrow> length (exec ii s stk) = n'"

end
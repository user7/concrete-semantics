theory Ch5
  imports Main
begin

(*
then = from this
thus = then show
hence = then have
*)

(*

see of and OF 4.4.4

f.simps refers to the whole list of recursion equations defining
f. Individual facts can be selected by writing f.simps(2), whole sublists by
writing f.simps(2−4).

*)

(*
show "P (n)"
proof (induction n)
  case 0            // let ?case = "P (0)"
  ..
  show ?case <proof>
next
  case (Suc n)      // fix n assume Suc: "P(n)"
                    // let ?case = "P (Suc n)"
  ..
  show ?case <proof>
qed

That is, if in the above proof we replace show "P (n)" by
show "A(n) \<Longrightarrow> P (n)" then case 0 stands for

  assume 0: "A(0)"
  let ?case = "P (0)"

and case (Suc n) stands for

  fix n
  assume Suc: "A(n) \<Longrightarrow> P (n)"
              "A(Suc n)"
  let ?case = "P (Suc n)"

page 64 induction trickery

*)

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set )"
proof
assume 0: "surj f"
from 0 have 1: "\<forall> A. \<exists> a. A = f a" by(simp add: surj_def)
from 1 have 2: "\<exists> a. {x . x \<notin> f x } = f a" by blast
from 2 show "False" by blast
qed

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set )"
proof
assume "surj f"
  hence "\<exists> a. {x . x \<notin> f x } = f a" by(auto simp: surj_def)
  thus "False" by blast
qed

(* 5.1 *)

lemma
  assumes TT: "\<forall> x y. T x y \<or> T y x"
    and A:    "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
    and TA:   "\<forall> x y. T x y \<longrightarrow> A x y"
    and A2:   "A x y"
  shows       "T x y"
proof (rule ccontr)
  assume Z: "\<not> T x y"
  from TT and this have "T y x" by auto
  from TA and this have "A y x" by auto
  from this and A2 have "A x y \<and> A y x" by auto
  from this and A have "x = y" by auto
  from this and TT and Z show "False" by auto
qed

(* 5.2 *)

lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  obtain n where nd: "n = (length xs) div 2" by auto
  obtain m where md: "m = (length xs) - n" by auto
  from md have mmin: "m \<le> length xs" by auto
  from nd and md have mneq: "m = n \<or> m = n + 1" by auto
  obtain ys where yd: "ys = take m xs" by auto
  obtain zs where zd: "zs = drop m xs" by auto
  from nd and yd and mmin have L1: "length ys = m" by auto
  from nd and md and zd have L2: "length zs = n" by auto
  from L1 and L2 and mneq have Lconj: "length ys = length zs \<or> length ys = length zs + 1" by auto
  from yd and zd have Conc: "xs = ys @ zs" by auto
  from Conc and Lconj show ?thesis by auto
qed

(* 5.3 *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> ev (n - 2)"
proof -
  assume "ev n"
  from this have "ev (n - 2)"
  proof cases
    case ev0 thus "ev(n - 2)" by (simp add: ev.ev0)
  next
    case (evSS k) thus "ev (n - 2)" by (simp add: ev.evSS)
  qed
  thus ?thesis by auto
qed

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof -
  show ?thesis using a
  proof cases
    case evSS thus ?thesis by auto
  qed
qed

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
  using a ev.cases by blast

(* 5.4 *)

lemma "\<not> ev (Suc 0)"
proof
  assume "ev (Suc 0)" then show False by cases
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  hence "ev (Suc 0)" by cases
  thus False by cases
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
  using ev.cases by auto

(*
Exercise 5.5. Recall predicate star from Section 4.5.2 and iter from Exer-
cise 4.4. Prove iter r n x y =\<Rightarrow> star r x y in a structured style; do not just
sledgehammer each case of the required induction.
*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
itern: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case iter0
  show ?case by (auto intro: refl)
next
  case itern
  thus ?case by (auto intro: step)
qed

(* 5.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = {x} \<union> elems xs"

value "elems ([1, 2, 5, 6]::nat list)"
value "elems ([]::nat list)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil thus ?case by auto
next
  case (Cons h xs0) show ?case
  proof cases
    assume hx: "h = x" then
    obtain ys where yd: "ys = ([]::'a list)" by auto
    hence "h \<notin> elems ys" by auto
    thus ?thesis using yd hx by blast
  next
    assume hnx: "h \<noteq> x"
    from hnx Cons.prems have inxs: "x \<in> elems xs0" by auto
    obtain ys0 zs where iyzs: "xs0 = ys0 @ x # zs \<and> x \<notin> elems ys0" using Cons.IH inxs by blast
    obtain ys where yd: "ys = h # ys0" by auto
    obtain xs where xd: "xs = h # xs0" by auto
    from hnx xd yd iyzs have wtf: "xs = ys @ x # zs \<and> x \<notin> elems ys" by auto
    from wtf xd show ?thesis by auto
  qed
qed

(* 5.7 *)

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

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced n Nil = (n = 0)" |
"balanced n (a#xs) = balanced (n + 1) xs" |
"balanced 0 (b#xs) = False" |
"balanced n (b#xs) = balanced (n - 1) xs"

value "balanced 0 [a, a, b, a, b, b, a, b]"

lemma "balanced n w = S (replicate n a @ w)"
  sorry

end
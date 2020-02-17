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

end
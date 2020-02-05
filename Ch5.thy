theory Ch5
  imports Main
begin

(*

see of and OF 4.4.4

f.simps refers to the whole list of recursion equations defining
f. Individual facts can be selected by writing f.simps(2), whole sublists by
writing f.simps(2−4).

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

end
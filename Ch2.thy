theory Ch2
  imports Main
begin

(* 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*
Exercise 2.2. Start from the definition of add given above. Prove that add
is associative and commutative. Define a recursive function double :: nat \<Rightarrow>
nat and prove double m = add m m.
*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

(*Ассоциативность*)
lemma "add (add a b) c = add a (add b c)"
  apply (induction a)
  apply (auto)
  done

(*1 доказалась сразу, добавить [simp]*)
lemma [simp]: "add n 0 = n"
  apply (induction n)
  apply (auto)
  done

(*2 добавить [simp]*)
lemma [simp]: "add b (Suc a) = add (Suc b) a"
  apply (induction b)
  apply (auto)
  done

(*Коммутативность*)
lemma "add a b = add b a"
  apply (induction a)
  apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma "double a = add a a"
  apply(induction a)
  apply(auto)
  done

(*
Exercise 2.3. Define a function count :: 0 a \<Rightarrow> 0 a list \<Rightarrow> nat that counts the
number of occurrences of an element in a list. Prove count x xs \<le> length xs.
*)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a Nil = 0" |
"count a (Cons x xs) = (if a = x then 1 else 0) + (count a xs)"

(* value "count 0 [0,4,5,0]" *)
value "count (0::nat) [0,4,5,0]"
value "count 0 [0::nat,4,5,0]"
value "count 0 ([0,4,5,0]::nat list)"

lemma "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

(*
Exercise 2.4. Define a recursive function snoc :: 0 a list \<Rightarrow> 0 a \<Rightarrow> 0 a list
that appends an element to the end of a list. With the help of snoc define
a recursive function reverse :: 0 a list \<Rightarrow> 0 a list that reverses a list. Prove
reverse (reverse xs) = xs.
*)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil a = (Cons a Nil)" |
"snoc (Cons x xs) a = Cons x (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

lemma rev_snoc [simp]: "reverse (snoc xs a) = Cons a (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

lemma "reverse (reverse m) = m" 
  apply(induction m)
  apply(auto)
  done

(*
Exercise 2.5. Define a recursive function sum_upto :: nat \<Rightarrow> nat such that
sum_upto n = 0 + ... + n and prove sum_upto n = n \<^emph> (n + 1) div 2.
*)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = n + 1 + (sum_upto n)"

lemma "sum_upto n = n * (n + 1) div 2" 
  apply(induction n)
  apply(auto)
  done

(*
Exercise 2.6. Starting from the type 0 a tree defined in the text, define a
function contents :: 0 a tree \<Rightarrow> 0 a list that collects all values in a tree in a
list, in any order, without removing duplicates. Then define a function sum_tree
:: nat tree \<Rightarrow> nat that sums up all values in a tree of natural numbers and
prove sum_tree t = sum_list (contents t ) (where sum_list is predefined).
*)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil" |
"contents (Node l a r) = (contents l) @ [a] @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = a + (sum_tree l) + (sum_tree r)"

lemma "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
  done

(*
Exercise 2.7. Define a new type 0 a tree2 of binary trees where values are
also stored in the leaves of the tree. Also reformulate the mirror function
accordingly. Define two functions pre_order and post_order of type 0 a tree2
\<Rightarrow> 0 a list that traverse a tree and collect all stored values in the respective
order in a list. Prove pre_order (mirror t ) = rev (post_order t ).
*)

datatype 'a tree2 = Leaf2 'a | Node2 "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leaf2 a) = Leaf2 a" |
"mirror2 (Node2 l a r) = Node2 (mirror2 r) a (mirror2 l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf2 a) = [a]" |
"pre_order (Node2 l a r) = (pre_order l) @ [a] @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf2 a) = [a]" |
"post_order (Node2 l a r) = (post_order r) @ [a] @ (post_order l)"

lemma "pre_order (mirror2 t) = post_order t"
  apply(induction t)
  apply(auto)
  done

(*
Exercise 2.8. Define a function intersperse :: 0 a \<Rightarrow> 0 a list \<Rightarrow> 0 a list such
that intersperse a [x 1 , ..., x n ] = [x 1 , a, x 2 , a, ..., a, x n ]. Now prove that
map f (intersperse a xs) = intersperse (f a) (map f xs).
*)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a Nil = Nil" |
"intersperse a (Cons x Nil) = Cons x Nil" |
"intersperse a (Cons x xs) = Cons x (Cons a (intersperse a xs))"

value "intersperse (9::nat) []"
value "intersperse (9::nat) [5]"
value "intersperse (9::nat) [1,2,3,4]"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

(*
Exercise 2.9. Write a tail-recursive variant of the add function on nat :
itadd. Tail-recursive means that in the recursive case, itadd needs to call
itself directly: itadd (Suc m) n = itadd . . .. Prove itadd m n = add m n.
*)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 m = m" |
"itadd (Suc n) m = itadd n (Suc m)"

lemma "itadd m n = add m n"
  apply(induction m arbitrary: n)
  apply(auto)
  done

(*
Exercise 2.10. Define a datatype tree0 of binary tree skeletons which do not
store any information, neither in the inner nodes nor in the leaves. Define a
function nodes :: tree0 \<Rightarrow> nat that counts the number of all nodes (inner
nodes and leaves) in such a tree. Consider the following recursive function:
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t )"
Find an equation expressing the size of a tree after exploding it (nodes
(explode n t )) as a function of nodes t and n. Prove your equation. You
may use the usual arithmetic operators, including the exponentiation opera-
tor “^”. For example, 2 ^ 2 = 4.
Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators.
*)

datatype tree0 = Leaf0 | Node0 tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf0 = 1" |
"nodes (Node0 l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

fun nexplode :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
"nexplode n t = 2 ^ n * nodes t + 2 ^ n - 1"

lemma "nodes (explode n t) = nexplode n t"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
  done

(* Как доказать это?
lemma "nexplode n t = nodes (explode n t)"
  apply(induction n arbitrary: t)
  apply(auto)
  done
*)

(*
Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int ) as a data type:
datatype exp = Var | Const int | Add exp exp | Mult exp exp
Define a function eval :: exp \<Rightarrow> int \<Rightarrow> int such that eval e x evaluates e at
the value x.
A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x 2 +3x 3 .
Define a function evalp :: int list \<Rightarrow> int \<Rightarrow> int that evaluates a polynomial at
the given value. Define a function coeffs :: exp \<Rightarrow> int list that transforms an
expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: evalp (coeffs e) x = eval e x.
Hint: consider the hint in Exercise 2.10.
*)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const i) _ = i" | 
"eval (Add e1 e2) x = eval e1 x + eval e2 x" |
"eval (Mult e1 e2) x = eval e1 x * eval e2 x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (Cons k ks) x = k + x * evalp ks x"

fun poly_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"poly_add [] ys = ys" |
"poly_add xs [] = xs" |
"poly_add (Cons x xs) (Cons y ys) = Cons (x + y) (poly_add xs ys)"

fun poly_sc_mul :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"poly_sc_mul k [] = []" |
"poly_sc_mul k (x # xs) = k * x # poly_sc_mul k xs"

fun poly_mul :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"poly_mul [] ys = []" |
"poly_mul (x # xs) ys = poly_add (poly_sc_mul x ys) (0 # poly_mul xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const i) = [i]" |
"coeffs (Add e1 e2) = poly_add (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = poly_mul (coeffs e1) (coeffs e2)"

lemma evalp_additive [simp]: "evalp (poly_add as bs) x = evalp as x + evalp bs x"
  apply(induction rule:poly_add.induct)
  apply(auto simp add:Int.int_distrib)
  done

lemma evalp_preserves_mul [simp]: "evalp (poly_sc_mul k as) x = k * evalp as x"
  apply(induction as)
  apply(auto simp add:Int.int_distrib)
  done

lemma evalp_multiplicative [simp]: "evalp (poly_mul as bs) x = evalp as x * evalp bs x"
  apply(induction as)
  apply(auto simp add:Int.int_distrib)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e)
  apply(auto)
  done

end
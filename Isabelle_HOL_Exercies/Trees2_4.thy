theory Trees2_4
imports Main
begin

datatype bdd = Leaf bool | Branch bdd bdd

(* eval accepts:
     - a function that can tell if a given variable
       number is true or false
     - a starting variable number. variables are numbered
       starting from 0 at root and increases gradually as
       we come down (ordered bdd).
     - a binary decision tree
   responds with the final truth value *)
primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool"
where
  "eval f n (Leaf b) = b"
| "eval f n (Branch l r) = (if f n then eval f (Suc n) r else eval f (Suc n) l)"

primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd"
where
  "bdd_unop f (Leaf a) = Leaf (f a)"
| "bdd_unop f (Branch l r) = Branch (bdd_unop f l) (bdd_unop f r)"

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd"
where
  "bdd_binop f (Leaf a) b = bdd_unop (f a) b"
| "bdd_binop f (Branch l r) b = (case b of
    Leaf a \<Rightarrow> Branch (bdd_binop f l b) (bdd_binop f r b)
  | Branch l' r' \<Rightarrow> Branch (bdd_binop f l l') (bdd_binop f r r'))"

theorem [simp]: "eval e n (bdd_unop f b) = f (eval e n b)"
  apply (induct b arbitrary:n)
  apply simp+
done

theorem [simp]:"eval e n (bdd_binop f b1 b2) = f (eval e n b1) (eval e n b2)"
  apply (induct b1 arbitrary:n b2)
  apply simp
  apply simp
  apply (case_tac b2)
  apply auto
done

(*
fun bdd_and :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
where
  "bdd_and b1 b2 = bdd_binop (\<lambda> x y. x \<and> y) b1 b2"
*)

definition bdd_and: "bdd_and \<equiv> bdd_binop op \<and>"
definition bdd_or: "bdd_or \<equiv> bdd_binop op \<or>"
definition bdd_not: "bdd_not \<equiv> bdd_unop Not"
definition bdd_xor: "bdd_xor b1 b2 \<equiv> bdd_or (bdd_and (bdd_not b1) b2) (bdd_and b1 (bdd_not b2))"

theorem [simp]: "eval e n (bdd_and b1 b2) = (eval e n b1 \<and> eval e n b2)"
  by (auto simp add:bdd_and)

theorem [simp]: "eval e n (bdd_or b1 b2) = (eval e n b1 \<or> eval e n b2)"
  by (auto simp add:bdd_or)

theorem [simp]: "eval e n (bdd_not b) = Not (eval e n b)"
  by (auto simp add:bdd_not)

theorem [simp]:"eval e n (bdd_xor b1 b2) = (let x = (eval e n b1) in let y = (eval e n b2) in (\<not>x \<and> y) \<or> (x \<and> \<not>y) )"
  by (auto simp add:bdd_xor bdd_and bdd_or bdd_not)

primrec bdd_var :: "nat \<Rightarrow> bdd"
where
  "bdd_var 0 = Branch (Leaf False) (Leaf True)"
| "bdd_var (Suc n) = Branch (bdd_var n) (bdd_var n)"

value "bdd_var 0"
value "bdd_var 1"
value "bdd_var 2"

theorem "\<forall> i . e i \<longrightarrow> eval e 0 (bdd_var i)"
(*Unsure about this one *)
oops

(* Solution copied from text *)
theorem [simp]: "\<forall> j. eval e j (bdd_var i) = e (i + j)"
  apply (induct i)
  apply auto
done

datatype form = T | Var nat | And form form | Xor form form

definition xor : "xor x y \<equiv> (\<not>x \<and> y) \<or> (x \<and> \<not>y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
where
  "evalf f T = True"
| "evalf f (Var n) = f n"
| "evalf f (And f1 f2) = (evalf f f1 \<and> evalf f f2)"
| "evalf f (Xor f1 f2) = xor (evalf f f1) (evalf f f2)"

fun mk_bdd :: "form \<Rightarrow> bdd"
where
  "mk_bdd T = Leaf True"
| "mk_bdd (Var n) = bdd_var n"
| "mk_bdd (And f1 f2) = bdd_and (mk_bdd f1) (mk_bdd f2)"
| "mk_bdd (Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)"

value "mk_bdd T"
value "mk_bdd (Var 1)"

theorem "eval e 0 (mk_bdd f) = evalf e f"
  apply (induct f)
  apply (auto simp add:xor)
done

end


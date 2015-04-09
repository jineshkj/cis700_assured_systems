
theory Lists1_9
imports Main
begin

(* Any alternatives for case ? *)
primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "zip1 [] ys = ys"
| "zip1 (x#xs) ys = (case ys of [] \<Rightarrow> x#xs | z#zs \<Rightarrow> [x,z] @ zip1 xs zs)"

value "zip1 [] []"
value "zip1 [1::int] [1]"
value "zip1 [1::int, 2, 3] [6]"
value "zip1 [1::int] [2, 3, 4]"

(* Any alternatives for case ? *)
primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "zip2 xs [] = xs"
| "zip2 xs (y#ys) = (case xs of [] \<Rightarrow> y#ys | z#zs \<Rightarrow> [z,y] @ zip1 zs ys)"

value "zip2 [] []"
value "zip2 [1::int] [1]"
value "zip2 [1::int, 2, 3] [6]"
value "zip2 [1::int] [2, 3, 4]"

fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "zipr [] ys = ys"
| "zipr xs [] = xs"
| "zipr (x#xs) (y#ys) =  [x,y] @ zipr xs ys"

value "zipr [] []"
value "zipr [1::int] [1]"
value "zipr [1::int, 2, 3] [6]"
value "zipr [1::int] [2, 3, 4]"

thm zipr.simps

lemma zip1_zip2: "zip1 xs ys = zip2 xs ys"
  apply (induct xs arbitrary:ys)
  apply (case_tac ys)
  apply simp
  apply simp
  apply simp
  apply (case_tac ys)
  apply simp
  apply simp
done

(* Used sledgehammer. Soln in text does not work *)
lemma zip2_zipr: "zip2 xs ys = zipr xs ys"
  apply (induct ys arbitrary: xs)
  apply (case_tac xs)
  apply simp+
  apply (case_tac xs)
  apply simp
  apply simp
by (metis zip1_zip2)

lemma zipr_zip1: "zipr xs ys = zip1 xs ys"
  by (simp add: zip1_zip2 zip2_zipr)

(* This needs some explanation *)
lemma "\<lbrakk> length p = length r ; length q = length s \<rbrakk> \<Longrightarrow> zipr (p@q) (r@s) = zipr p r @ zipr q s"
  apply (induct p arbitrary: q r s)
  apply auto
  apply (case_tac r)
  apply auto
done

end


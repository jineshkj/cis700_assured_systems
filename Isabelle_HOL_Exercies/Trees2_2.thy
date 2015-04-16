
theory Trees2_2
imports Main
begin

(* copied from question *)
primrec sum :: "nat list \<Rightarrow> nat"
where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

theorem sum_foldr: "sum xs = foldr (op +) xs 0"
  apply (induct xs)
  apply simp
  apply simp
done

theorem length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  apply (induct xs)
  apply simp
  apply simp
done

theorem "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda> x res. res + x + 3) xs 0"
  apply (induct xs)
  apply simp
  apply simp
done

theorem "foldr g (map f xs) a = foldr (\<lambda> x res. (g (f x) res)) xs a"
  apply (induct xs)
  apply simp
  apply simp
done

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list"
where
  "rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

value "rev_acc [] []"
value "rev_acc [1,2] []"
value "rev_acc [] [1,2]"
value "rev_acc [1,2] [3,4]"

theorem rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  apply (induct xs arbitrary:a)
  apply simp
  apply simp
done

theorem sum_append[simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
  apply simp
  apply simp
done


(* Unclear how the problem was solved in text *)
theorem foldr_append: "foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
  quickcheck
oops

(*
primrec prod :: "nat list \<Rightarrow> nat"
where
  "prod [] = 1"
| "prod (x#xs) = x * prod xs"
*)

definition prod: "prod xs \<equiv> foldr (op *) xs (1::nat)"

value "prod []"
value "prod [2]"
value "prod [1,2,3]"

(* FIXME: unable to prove this lemma *)
theorem "prod (xs @ ys) = prod xs * prod ys"
oops

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

value "Tip"
value "Node Tip 2 Tip"

primrec preorder :: "'a tree \<Rightarrow> 'a list"
where
  "preorder Tip = []"
| "preorder (Node l v r) = (v # preorder l) @ preorder r"

value "preorder Tip"
value "preorder (Node (Node Tip 3 Tip) 2 (Node Tip 4 Tip))"

primrec postorder :: "'a tree \<Rightarrow> 'a list"
where
  "postorder Tip = []"
| "postorder (Node l v r) = (postorder l) @ (postorder r) @ [v]"

value "postorder Tip"
value "postorder (Node (Node Tip 3 Tip) 2 (Node Tip 4 Tip))"

fun postorder_acc:: "['a tree, 'a list] \<Rightarrow> 'a list"
where
  "postorder_acc Tip acc = acc"
| "postorder_acc (Node l v r) acc = (postorder_acc l (postorder_acc r (v#acc)))"

value "postorder_acc Tip []"
value "postorder_acc (Node (Node Tip 3 Tip) 2 (Node Tip 4 Tip)) []"

theorem "postorder_acc t xs = (postorder t) @ xs"
  apply (induct t arbitrary:xs)
  apply simp+
done

fun foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b"
where
  "foldl_tree f acc Tip = acc"
| "foldl_tree f acc (Node l v r) = foldl_tree f (foldl_tree f (f acc v) r) l"


theorem "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
  apply (induct t)
  apply simp
  apply simp
done

primrec tree_sum :: "nat tree \<Rightarrow> nat"
where
  "tree_sum Tip = 0"
| "tree_sum (Node l v r) = v + (tree_sum l) + (tree_sum r)"

theorem "tree_sum t = sum (preorder t)"
  apply (induct t)
  apply simp+
done

end


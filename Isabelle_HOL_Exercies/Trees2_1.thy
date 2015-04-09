
theory Trees2_1
imports Main
begin

datatype 'a tree = Leaf 'a | Node 'a "'a tree" "'a tree"

value "Leaf 1"
value "Node 2 (Leaf 1) (Leaf 2)"

primrec preOrder :: "'a tree \<Rightarrow> 'a list"
where
  "preOrder (Leaf a) = [a]"
| "preOrder (Node a b c) = (a # preOrder b) @ preOrder c"

value "preOrder (Leaf 1)"
value "preOrder (Node 2 (Leaf 1) (Leaf 3))"

primrec postOrder :: "'a tree \<Rightarrow> 'a list"
where
  "postOrder (Leaf a) = [a]"
| "postOrder (Node a b c) = (postOrder b) @ (postOrder c) @ [a]"

value "postOrder (Leaf 1)"
value "postOrder (Node 2 (Leaf 1) (Leaf 3))"

primrec inOrder :: "'a tree \<Rightarrow> 'a list"
where
  "inOrder (Leaf a) = [a]"
| "inOrder (Node a b c) = (inOrder b) @ [a] @ (inOrder c)"

value "inOrder (Leaf 1)"
value "inOrder (Node 2 (Leaf 1) (Leaf 3))"

primrec mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "mirror (Leaf a) = (Leaf a)"
| "mirror (Node a b c) = Node a (mirror c) (mirror b)"


value "mirror (Leaf 1)"
value "mirror (Node 2 (Leaf 1) (Leaf 3))"

theorem "preOrder (mirror t) = rev (postOrder t)"
  apply (induct t)
  apply auto
done

theorem "postOrder (mirror t) = rev (preOrder t)"
  apply (induct t)
  apply auto
done

theorem "inOrder (mirror t) = rev (inOrder t)"
  apply (induct t)
  apply auto
done

primrec root :: "'a tree \<Rightarrow> 'a"
where
  "root (Leaf a) = a"
| "root (Node a b c) = a"

value "root (Leaf 1)"
value "root (Node 2 (Leaf 1) (Leaf 3))"

primrec leftmost :: "'a tree \<Rightarrow> 'a"
where
  "leftmost (Leaf a) = a"
| "leftmost (Node a b c) = leftmost b"

value "leftmost (Leaf 1)"
value "leftmost (Node 2 (Leaf 1) (Leaf 3))"

primrec rightmost :: "'a tree \<Rightarrow> 'a"
where
  "rightmost (Leaf a) = a"
| "rightmost (Node a b c) = rightmost c"

value "rightmost (Leaf 1)"
value "rightmost (Node 2 (Leaf 1) (Leaf 3))"

lemma [simp]: "inOrder xt \<noteq> []"
  apply (induct_tac xt)
  apply auto
done

theorem "last (inOrder t) = rightmost t"
  apply (induct t)
  apply simp
  (* inOrder t2 = [] \<longrightarrow> a = rightmost t2
        can be proven by showing inOrder t2 \<noteq> [] *)
  apply simp
done

theorem "hd (inOrder xt) = leftmost xt"
  apply (induct xt)
  apply simp
  apply simp
done

theorem "hd (preOrder xt) = last (postOrder xt)"
  apply (induct xt)
  apply simp
  apply simp
done

theorem "hd (preOrder xt) = root xt"
  apply (induct xt)
  apply simp
  apply simp
done

theorem "hd (inOrder xt) = root xt"
  quickcheck
oops

theorem "last (postOrder xt) = root xt"
  apply (induct xt)
  apply simp
  apply simp
done

end


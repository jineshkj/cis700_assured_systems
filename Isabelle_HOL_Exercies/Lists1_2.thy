
theory Lists1_2
imports Main
begin

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "replace x y [] = []" |
  "replace x y (z # zs) = (if x = z then (y # (replace x y zs)) else (z # (replace x y zs)))"

lemma rev_replace_append: "replace x y (xs @ ys) = (replace x y xs) @ (replace x y ys)"
  apply (induct_tac xs)
  apply auto
done

lemma "rev(replace x y zs) = replace x y (rev zs)"
  apply (induct_tac zs)
  apply (auto simp add:rev_replace_append)
done

lemma "replace x y (replace u v zs) = replace u v (replace x y zs)"
  quickcheck
oops

lemma "replace y z (replace x y zs) = replace x z zs"
  quickcheck
oops

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "del1 x [] = []" |
  "del1 x (y # ys) = (if x = y then ys else (y # (del1 x ys)))"

primrec delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "delall x [] = []" |
  "delall x (y # ys) = (if x = y then [] else [y]) @ (delall x ys)"

theorem testth_1: "del1 x (delall x xs) = delall x xs"
  apply (induct xs)
  apply auto
done

theorem "delall x (delall x xs) = delall x xs"
  apply (induct xs)
  apply auto
done

theorem "delall x (del1 x xs) = delall x xs"
  apply (induct xs)
  apply auto
done

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  apply (induct zs)
  apply auto
done

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  apply (induct zs)
  apply simp
  apply (simp add:testth_1)
done

theorem "delall x (delall y zs) = delall y (delall x zs)"
  apply (induct zs)
  apply auto
done

theorem "del1 y (replace x y xs) = del1 x xs"
  quickcheck
oops

theorem "delall y (replace x y xs) = delall x xs"
  quickcheck
oops

theorem "replace x y (delall x zs) = delall x zs"
  apply (induct zs)
  apply auto
done

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
  quickcheck
oops

theorem "rev(del1 x xs) = del1 x (rev xs)"
  quickcheck
oops

lemma delall_1: "delall x (xs @ ys) = (delall x xs) @ (delall x ys)"
  apply (induct xs)
  apply auto
done

theorem "rev(delall x xs) = delall x (rev xs)"
  apply (induct xs)
  apply (simp add:delall_1)+
done

end


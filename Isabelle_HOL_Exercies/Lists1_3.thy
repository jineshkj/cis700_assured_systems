
theory Lists1_3
imports Main
begin

primrec alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "alls P [] = True" |
  "alls P (x # xs) = (if (P x) then (alls P xs) else False)"

primrec exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "exs P [] = False" |
  "exs P (x # xs) = (if (P x) then True else (exs P xs))"

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  apply (induct xs)
  apply auto
done

lemma alls_append: "alls P (xs @ ys) = ((alls P xs) \<and> (alls P ys))"
  apply (induct xs)
  apply simp+
done

lemma "alls P (rev xs) = alls P xs"
  apply (induct xs)
  apply simp
  apply (simp add:alls_append)
done

lemma "exs (\<lambda>x. Px \<and> Qx) xs = (exs P xs \<and> exs Q xs)"
  quickcheck
oops

lemma "exs P (map f xs) = exs (P o f) xs"
  apply (induct xs)
  apply auto
done

lemma exs_append: "exs P (xs @ ys) = ((exs P xs) \<or> (exs P ys))"
  apply (induct xs)
  apply simp+
done

lemma "exs P (rev xs) = exs P xs"
  apply (induct xs)
  apply simp
  apply (simp add:exs_append)
done

lemma "exs (\<lambda>x. P x \<or> Q x) xs = ((exs P xs) \<or> (exs Q xs))"
  apply (induct xs)
  apply auto
done

lemma "exs P xs = (\<not> alls (\<lambda>x. \<not>(P x)) xs)"
  apply (induct xs)
  apply auto
done

primrec is_in :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "is_in x [] = False" |
  "is_in x (y # ys) = (if x = y then True else (is_in x ys))"

value "is_in 1 [1,2,3]"
value "is_in 1"

theorem "is_in a xs = exs (\<lambda>x. is_in a [x]) xs"
  apply (induct xs)
  apply simp+
done

primrec nodups :: "'a list \<Rightarrow> bool"
where
  "nodups [] = True" |
  "nodups (x # xs) = (if (is_in x xs) then False else (nodups xs))"

value "nodups [1,1]"

primrec deldups :: "'a list \<Rightarrow> 'a list"
where
  "deldups [] = []"
| "deldups (x # xs) = (if (is_in x xs) then (deldups xs) else (x # (deldups xs)))"

value "deldups [1,1]"

lemma "length (deldups xs) \<le> length xs"
  apply (induct xs)
  apply simp+
done

lemma is_in_deldups: "is_in a (deldups xs) \<longrightarrow> is_in a xs"
  apply (induct xs)
  apply simp
  apply simp
done

lemma "nodups (deldups xs)"
  apply (induct xs)
  apply simp
  apply (simp add:is_in_deldups)
done

lemma "deldups (rev xs) = rev (deldups xs)"
  quickcheck
oops

end


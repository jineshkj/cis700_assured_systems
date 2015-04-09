
theory Lists1_5
imports Main
begin

primrec occurs:: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
  "occurs x [] = 0"
| "occurs x (y#ys) = (if x = y then Suc (occurs x ys) else (occurs x ys))"

value "occurs 1 [1,2,3,4,1,3::int]"

lemma occurs_append: "occurs x (ys @ zs) = (occurs x ys) + (occurs x zs)"
  apply (induct ys)
  apply auto
done

lemma "occurs x ys = occurs x (rev ys)"
  apply (induct ys)
  apply (auto simp add:occurs_append)
done

lemma "occurs x ys \<le> length ys"
  apply (induct ys)
  apply auto
done

lemma "occurs a (map f xs) = occurs (f a) xs"
  quickcheck
oops

lemma "occurs a (filter P xs) = (if P a then occurs a xs else 0)"
  apply (induct xs)
  apply auto
done

primrec remDups :: "'a list \<Rightarrow> 'a list"
where
  "remDups [] = []"
| "remDups (x#xs) = (if 0 < occurs x xs then remDups xs else (x#(remDups xs)))"

value "remDups [1,2,3,4,5::int,1,2,5]"

(* different from text *)
lemma occurs_remdups: "occurs x (remDups xs) = (if ((occurs x xs) = 0) then 0 else 1)"
  apply (induct xs)
  apply auto
done

(* different from text *)
primrec unique:: "'a list \<Rightarrow> bool"
where
  "unique [] = True"
| "unique (x#xs) = (if 0 < occurs x xs then False else unique xs)"

value "unique []"
value "unique [1::int,2,3]"
value "unique [1::int,1,2,3]"

lemma "unique (remDups xs)"
  apply (induct xs)
  apply (auto simp add:occurs_remdups)
done

end


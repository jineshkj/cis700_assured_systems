
theory Lists1_1
imports Main
begin

primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
where
"snoc [] y = [y]" |
"snoc (x # xs) y = (x # (snoc xs y))"

value "snoc [2,3] 1"

lemma snoc_append: "snoc xs x = xs @ [x]"
apply (induct_tac xs)
apply auto
done

lemma rev_cons: "rev (x # xs) = snoc (rev xs) x"
apply (induct_tac xs)
apply simp
apply (simp add:snoc_append)
done

end


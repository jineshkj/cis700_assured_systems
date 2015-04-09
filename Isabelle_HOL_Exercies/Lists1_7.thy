
theory Lists1_7
imports Main
begin

primrec list_union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_union [] ys = ys"
| "list_union (x#xs) ys = (let result = list_union xs ys in if x : set result then result else x#result)"

value "list_union [] []"
value "list_union [] [1]"
value "list_union [1] []"
value "list_union [1::int,2,3] [2,3,4]"

lemma "set (list_union xs ys) = set xs \<union> set ys"
  apply (induct xs)
  apply simp
  apply (simp add:Let_def)
  apply auto
done

value "distinct [1::int,1]"

lemma [rule_format]:"distinct xs \<longrightarrow> distinct ys \<longrightarrow> distinct (list_union xs ys)"
  apply (induct xs)
  apply (simp add:Let_def)+
done

lemma "((\<forall>x \<in> A. P x) \<and> (\<forall>x \<in> B. P x)) \<longrightarrow> (\<forall>x \<in> A \<union> B. P x)"
  by auto

lemma "\<forall>x \<in> A. Q (f x) \<Longrightarrow> \<forall>y \<in> f ` A. Q y"
  by auto


end


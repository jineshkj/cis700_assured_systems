
theory Lists1_4
imports Main
begin

primrec first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"
where
  "first_pos P [] = 0"
| "first_pos P (x#xs) = (if (P x) then 0 else (Suc (first_pos P xs)))"

lemma "first_pos (\<lambda>x. x=3) [1::nat,3,5,3,1] = 1"
  by auto

lemma "first_pos (\<lambda>x. x > 4) [1::nat, 3, 5, 7] = 2"
  by auto

lemma "first_pos (\<lambda>x. (length x) > 1) [[], [1, 2], [3]] = 1"
  by auto

(* different from text *)
lemma "list_all (\<lambda>x. \<not>P x) xs \<longrightarrow> first_pos P xs = length xs"
  apply (induct xs)
  apply simp+
done

value "take 3 [1::int,1,2,3]"

lemma "list_all (\<lambda>x. \<not>P x) (take (first_pos P xs) xs)"
  apply (induct xs)
  apply simp+
done

lemma "first_pos (\<lambda>x. P x \<or> Q x) xs = (min (first_pos P xs) (first_pos Q xs))"
  apply (induct xs)
  apply simp+
done

lemma "first_pos (\<lambda>x. P x \<and> Q x) xs \<ge> (max (first_pos P xs) (first_pos Q xs))"
  apply (induct xs)
  apply simp+
done

(* different from text *)
lemma "(list_all P xs) \<longrightarrow> (list_all Q xs) \<longrightarrow> (first_pos P xs \<ge> first_pos Q xs)"
  apply (induct xs)
  apply simp+
done

primrec count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"
where
  "count P [] = 0"
| "count P (x#xs) = (if (P x) then Suc (count P xs) else count P xs)"

value "count (\<lambda>x. x>2) [3::nat]"
value "count (\<lambda>x. x>2) [1::nat,2,3,4,5]"

lemma count_append: "count P (xs@ys) = count P xs + count P ys"
  apply (induct xs)
  apply simp+
done

lemma "count P xs = count P (rev xs)"
  apply (induct xs)
  apply (simp add:count_append)+
done

value "filter (\<lambda>x. x>2) [1,2,3,4,5::int]"

lemma "length (filter P xs) = count P xs"
  apply (induct xs)
  apply simp+
done

end


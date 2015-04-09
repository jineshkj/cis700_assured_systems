
theory Lists1_6
imports Main
begin

primrec sum :: "nat list \<Rightarrow> nat"
where
  "sum [] = 0"
| "sum (x#xs) = x + (sum xs)"

value "sum [1::nat,2]"

primrec flatten :: "'a list list \<Rightarrow> 'a list"
where
  "flatten [] = []"
| "flatten (x#xs) = x @ (flatten xs)"

value "flatten []"
value "flatten [[]]"
value "flatten [[],[1,2],[1,3]]"

lemma "sum [2::nat, 4, 8] = 14"
  by auto

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = [2::nat,3,4,5,7,9]"
  by auto

lemma "length (flatten xs) = sum (map length xs)"
  apply (induct xs)
  apply simp+
done

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
    apply simp
  apply (induct ys)
  apply simp+
done

lemma flatten_append: "flatten (xs @ ys) = flatten xs @ flatten ys"
  apply (induct xs)
  apply (induct ys)
  apply simp+
done

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
  apply (induct xs)
  apply (simp add:flatten_append)+
done

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
  apply (induct xs)
  apply (simp add:flatten_append)+
done

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
  apply (induct xs)
  apply simp+
done

lemma "flatten (rev xs) = flatten xs"
  quickcheck
oops

lemma "sum (rev xs) = sum xs"
  apply (induct xs)
  apply (simp add:sum_append)+
done

lemma "list_all (\<lambda>x. x\<ge>1) xs \<longrightarrow> length xs \<le> sum xs"
  apply (induct xs)
  apply auto
done

primrec list_exists:: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_exists P [] = False"
| "list_exists P (x#xs) = (P x \<or> list_exists P xs)"

value "list_exists (\<lambda>x. x=3) []"
value "list_exists (\<lambda>x. x=3) [3]"
value "list_exists (\<lambda>x. x=3) [1::int,3]"

lemma "list_exists (\<lambda>n. n < 3) [4::nat, 3, 7] = False"
  by auto

lemma "list_exists (\<lambda>n. n < 4) [4::nat, 3, 7] = True"
  by auto

lemma list_exists_append: "list_exists P (xs@ys) = (list_exists P xs \<or> list_exists P ys)"
  apply (induct ys)
    apply simp
  apply (induct xs)
  apply simp
  apply auto
done

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
  apply (induct xs)
  apply (simp add:list_exists_append)+
done

definition list_exists2 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_exists2 P xs == \<not> list_all (\<lambda>x. \<not> P x) xs"

lemma "list_exists P xs = list_exists2 P xs"
  apply (induct xs)
  apply (simp add:list_exists2_def)+
done

end


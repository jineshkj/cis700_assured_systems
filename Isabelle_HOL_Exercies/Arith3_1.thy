
theory Arith3_1
imports Main
begin

primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "pow x 0 = 1"
| "pow x (Suc n) = x * (pow x n)"

lemma pow_add: "pow x (m + n) = pow x m * pow x n"
  apply (induct m)
  apply auto
done

theorem "pow (pow x m) n = pow x (m * n)"
  apply (induct n arbitrary:m)
  apply (simp add:pow_add)+
done

primrec sum :: "nat list \<Rightarrow> nat"
where
  "sum [] = 0"
| "sum (x#xs) = x + sum xs"

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
  apply auto
done

theorem "sum (rev xs) = sum xs"
  apply (induct xs)
  apply simp
  apply (simp add:sum_append)
done

fun Sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat  \<Rightarrow> nat"
where
  "Sum f 0 = 0"
| "Sum f (Suc n) = f n + Sum f n"

theorem "Sum (\<lambda> i. f i + g i) n = Sum f n + Sum g n"
  apply (induct n)
  apply simp+
done

value "Sum (\<lambda>x. x) 0"
value "Sum (\<lambda>x. x) 4"

theorem "Sum f (k + l) = Sum f k + Sum (\<lambda> i. f (k + i))  l"
  apply (induct l)
  apply simp+
done

value "map (\<lambda>x. x) [1,2]"

theorem "Sum f n = sum (map f [0..<n])"
  apply (induct n)
  apply (simp add:sum_append)+
done


end



theory Lists1_8
imports Main
begin

primrec ListSum :: "nat list \<Rightarrow> nat"
where
  "ListSum [] = 0"
| "ListSum (x#xs) = x + ListSum xs"

value "ListSum []"
value "ListSum [1]"
value "ListSum [1,1,2]"

value "[0..<4]"
value "ListSum [0..<Suc 0]"

lemma listsum_append: "ListSum (xs @ ys) = ListSum xs + ListSum ys"
  apply (induct xs)
  apply simp
  apply auto
done

theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
  apply (induct n)
  apply (simp add:listsum_append)+
done

value "replicate 10 (1::nat)"

theorem "ListSum (replicate n a) = n * a"
  apply (induct n)
  apply simp
  apply simp
done

fun ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
where
  "ListSumTAux [] n = n"
| "ListSumTAux (x#xs) n = ListSumTAux xs (n + x)"

value "ListSumTAux [] 0"
value "ListSumTAux [1] 0"
value "ListSumTAux [1,2] 0"

fun ListSumT :: "nat list \<Rightarrow> nat"
where
  "ListSumT xs = ListSumTAux xs 0"

value "ListSumT []"
value "ListSumT [1]"
value "ListSumT [1,2]"

lemma list_sumtaux_add: "\<forall> a b. ListSumTAux xs (a + b) = a + ListSumTAux xs b"
  apply (induct xs)
  apply auto
done

(* Proving the lemma with reversed sides does not help in proving
   the main lemma proved later *)
lemma list_sumtaux_val: "a + ListSumTAux xs 0 = ListSumTAux xs a"
  apply (induct xs)
  (* using [[simp_trace=true]] *)
  apply simp
  apply (simp add:list_sumtaux_add)
done

theorem "ListSum xs = ListSumT xs"
  apply (induct xs)
  apply simp
  (* using [[simp_trace = true]] *)
  apply (simp add:list_sumtaux_val)
done


end


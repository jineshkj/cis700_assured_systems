
theory Trees2_3
imports Main
begin

datatype tree = Tp | Nd tree tree

primrec tips :: "tree \<Rightarrow> nat"
where
  "tips Tp = 1"
| "tips (Nd l r) = (tips l) + (tips r)"

primrec height :: "tree \<Rightarrow> nat"
where
  "height Tp = 0"
| "height (Nd l r) = 1 + max (height l) (height r)"

primrec cbt :: "nat \<Rightarrow> tree"
where
  "cbt 0 = Tp"
| "cbt (Suc n) = Nd (cbt n) (cbt n)"

primrec iscbt ::"(tree \<Rightarrow> 'a) \<Rightarrow> tree \<Rightarrow> bool"
where
  "iscbt f Tp = True"
| "iscbt f (Nd l r) = ((iscbt f l) \<and> (iscbt f r) \<and> (f l = f r))"

value "iscbt tips Tp"
value "iscbt tips (Nd Tp Tp)"

value "size Tp"
value "size (Nd Tp Tp)"

lemma tips_size: "tips t = 1 + size t"
  apply (induct t)
  apply auto
done

theorem iscbt_tips_size: "iscbt tips t = iscbt size t"
  apply (induct t)
  apply simp
  apply (simp add:tips_size)
done

value "height Tp"
value "size Tp"

value "height (Nd Tp Tp)"
value "size (Nd Tp Tp)"

value "height (Nd (Nd Tp Tp) (Nd Tp Tp))"
value "size (Nd (Nd Tp Tp) (Nd Tp Tp))"

lemma height_tips: "iscbt height t \<longrightarrow> tips t = (2 ^ height t)"
  apply (induct t)
  apply simp
  apply auto
done

theorem iscbt_height_tips: "iscbt height t = iscbt tips t"
  apply (induct t)
  apply simp
  apply (auto simp add:height_tips)
done

(* Can we prove the same using induction as well ? *)
theorem "iscbt size t = iscbt height t"
  by (simp add:iscbt_height_tips iscbt_tips_size)

end


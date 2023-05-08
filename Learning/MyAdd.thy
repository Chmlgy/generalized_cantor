theory MyAdd
imports Main
begin

datatype nat = zero | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add zero n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m zero = m"
  apply(induction m)
  apply(auto)
  done

theorem add_assoc: "add (add m n) l = add m (add n l)"
  apply(induction m)
  apply(auto)
  done

lemma add_Suc2 [simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
  apply(auto)
  done

theorem add_comm: "add m n = add n m"
  apply(induction m)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double zero = zero" |
"double (Suc m) = Suc (Suc (double m))"

theorem double_add2: "double m = add m m"
  apply(induction m)
  apply(auto)
  done

end

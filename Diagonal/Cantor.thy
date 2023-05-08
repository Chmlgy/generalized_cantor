theory Cantor imports Main HOL.Fun
begin

(* 1.
  S x T ---- f ----> Y
    ^                |
    |                |
(beta, Id)         alpha             S ---- beta_comp ----> T              beta \<circ> beta_comp = Id  
    |                |
    |                v
    T   ---- g ----> Y
*)
theorem "Abstracted_Cantor":
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> 'c" and \<alpha> :: "'c \<Rightarrow> 'c" and \<beta> :: "'a \<Rightarrow> 'b" and \<beta>_c :: "'b \<Rightarrow> 'a"
  assumes surjectivity: "surj f"
  and no_fixed_point: "\<forall>y. \<alpha> y \<noteq> y"
  and right_inverse: "\<forall>s. \<beta> (\<beta>_c s) = s"
  shows "False"
proof -
  from surjectivity have "\<forall>h :: 'a \<Rightarrow> 'c. \<exists>t. h = f t" by auto
  hence "\<exists>t. (\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) = f t" by simp
  then obtain t0 where "(\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) = f t0" ..
  hence "(\<alpha> \<circ> (\<lambda>t'. f (\<beta> t') t')) (\<beta>_c t0) = f t0 (\<beta>_c t0)" by (rule arg_cong)
  (*hence "\<alpha> (f (\<beta> (\<beta>_c t0)) (\<beta>_c t0)) = f t0 (\<beta>_c t0)" by simp*)
  hence "\<alpha> (f t0 (\<beta>_c t0)) = f t0 (\<beta>_c t0)" using right_inverse by simp
  thus "False" using no_fixed_point by simp
qed


(* 2.
  T x T ---- f ----> Y
    ^                |
    |                |
 Diagonal          alpha  
    |                |
    |                v
    T   ---- g ----> Y
*)
theorem "Generalized_Cantor":
  fixes alpha :: "'b \<Rightarrow> 'b" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes surjectivity: "surj f"
  and no_fixed_point: "\<forall>y. alpha y \<noteq> y"
  shows "False"
(*proof -
  from surjectivity have "\<forall>h :: 'a \<Rightarrow> 'b. \<exists>t. h = f t" by (auto simp add: surj_def)
  hence "\<exists>t. (alpha \<circ> (\<lambda>t'. f t' t')) = f t" by simp
  then obtain t0 where "(alpha \<circ> (\<lambda>t'. f t' t')) = f t0" ..
  hence "(alpha \<circ> (\<lambda>t'. f t' t')) t0 = f t0 t0" by (rule arg_cong)
  hence "alpha (f t0 t0) = f t0 t0" by simp
  thus "False" using no_fixed_point by simp
qed*)
  apply(rule Abstracted_Cantor[of f alpha "\<lambda>x. x" "\<lambda>x. x"])
  apply(auto simp add: no_fixed_point surjectivity)
  done


(* 3.
  T ---- f ----> \<P>(T)
*)
fun not :: "bool \<Rightarrow> bool" where
"not True = False" |
"not False = True"

theorem "Classic_Cantor":
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Generalized_Cantor[of f not])
  apply(auto simp add: surjectivity)
  done


(* 4.
  |\<nat>| < |\<P>(\<nat>)|
*)
theorem "Classic_Nat_Cantor":
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Classic_Cantor[of f])
  apply(simp add: surjectivity)
  done

end

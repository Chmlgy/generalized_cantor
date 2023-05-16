section \<open> Generalized Cantor's Theorem and Instances  \<close>

theory GeneralCantor imports Complex_Main "HOL-Analysis.Analysis" "HOL-ZF.HOLZF"
begin

text \<open>
  1. The most abstracted version of Cantor's theorem.
  S x T ---- f ----> Y
    ^                |
    |                |
(beta, Id)         alpha             S ---- beta_comp ----> T              beta \<circ> beta_comp = Id  
    |                |
    |                v
    T   ---- g ----> Y
\<close>
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
  hence "\<alpha> (f t0 (\<beta>_c t0)) = f t0 (\<beta>_c t0)" using right_inverse by simp
  thus "False" using no_fixed_point by simp
qed


text \<open>
  2. An instance of the above theorem, where S = T and \<beta> = Id. Still a quite general version
  of Cantor's theorem.
  T x T ---- f ----> Y    f x y = not elem x y
    ^                |
    |                |
 Diagonal          alpha
    |                |
    |                v
    T   ---- g ----> Y
\<close>
theorem "Generalized_Cantor":
  fixes alpha :: "'b \<Rightarrow> 'b" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes surjectivity: "surj f"
  and no_fixed_point: "\<forall>y. alpha y \<noteq> y"
  shows "False"
  apply(rule Abstracted_Cantor[of f alpha "\<lambda>x. x" "\<lambda>x. x"])
  apply(auto simp add: no_fixed_point surjectivity)
  done


text \<open>
  3. An instance of the above version of Cantor's theorem, where 'b = bool and \<alpha> = \<not>.
  Entailing the fact that no surjective functions exists from a set to its power set.
  T ---- f ----> \<P>(T)
\<close>
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


text \<open>
  4. An instance of the above theorem. With the set 'a being natural numbers.
 |\<P>(\<nat>)| > |\<nat>|                                                                                   
\<close>
theorem "Classic_Nat_Cantor":
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Classic_Cantor[of f])
  apply(simp add: surjectivity)
  done


text \<open>
  5. Contrapositive of Cantor's Theorem:
  If Y is a set and there exists a set T together with a function f: T x T \<longrightarrow> Y
  such that all functions g: T \<longrightarrow> Y are representable by f, i.e. there exists
  a t in T such that g = f t, then all functions \<alpha>: Y \<longrightarrow> Y admits a fixed point.
\<close>
theorem "Contrapositive_Cantor":
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes surjectivity: "surj f"
  shows "\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y"
  by (meson Generalized_Cantor surjectivity)


text \<open> 
  6. All endomorphisms admitting a fixed point means the set has only one element.
  Still, we will keep the definition of fixed points and do not make assumptions on the cardinality
  of Y. The reason being that fixed points easily generalize to categories unlike cardinality.
\<close>
(* TODO:
lemma "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longleftrightarrow> (\<forall>a b :: 'b. a = b)"
  apply(auto)
*)


text \<open>
 7. |\<real>| = |\<P>(\<nat>)|
\<close>

text \<open>
  7.1 Show that \<exists>f s.t. f: \<real> \<longlongrightarrow> \<P>(\<rat>) and f is injective. ==> |\<real>| \<le> 2^(\<aleph>_0)
\<close>
definition cut_set :: "real \<Rightarrow> (rat \<Rightarrow> bool)" where
"cut_set r = (\<lambda>q. of_rat q < r)"

lemma "contra_inj_cut_set": "\<forall>x y :: real. x \<noteq> y \<longrightarrow> cut_set x \<noteq> cut_set y"
  by (metis cut_set_def linorder_less_linear of_rat_dense order_less_not_sym)

lemma "inj_example_cut_set": "inj cut_set"
  by (meson contra_inj_cut_set injI)

lemma "\<exists>f :: real \<Rightarrow> (rat \<Rightarrow> bool). inj f"
  by (meson inj_example_cut_set)


text \<open>
  7.2 Show that \<exists>f s.t. f: (nat => bool) => real and f is surjective on [0, 1]. \<Longrightarrow> 2^(\<aleph>_0) \<ge> |[0,1]|
\<close>
(*A function that is surjective on real numbers between 0 and 1: *)
definition seq_to_real :: "(nat \<Rightarrow> bool) \<Rightarrow> real" where
"seq_to_real f = \<Sum>{1/(2^n) | n. f n = True}"

(*Helper definition and functions to prove that the above function is surjective: *)
(*A function that returns the most significant decimal binary digit for a real number between 0 and 1: *)
definition most_sig_bdig :: "real \<Rightarrow> nat" where
"most_sig_bdig x = Min {n. 1/(2^n) < x}" 

definition bool_mult :: "bool \<Rightarrow> real \<Rightarrow> real" where
"bool_mult b x = (if b = False then 0 else x)"

(*A function that expands a real number between 0 and 1 to its binary representation*)
definition binary_remainder :: "(real \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real set" where
"binary_remainder bs x n = {bool_mult (bs x k)  1/(2^k) | k. 1 < k \<and> k < n}"

lemma [fundef_cong]: assumes "x = x'" and "n = n'" and "\<And>k. k < n \<Longrightarrow> bs x k = bs' x k" shows "binary_remainder bs x n = binary_remainder bs' x' n'"
  using assms unfolding binary_remainder_def
  by force

fun binary_sequence :: "real \<Rightarrow> nat \<Rightarrow> bool" where
"binary_sequence x 0 = (if most_sig_bdig x > 1 then False else True)" |
binseq_rem: "binary_sequence x (Suc n) = (if most_sig_bdig (x - \<Sum>(binary_remainder binary_sequence x n)) > Suc n 
                              then False else True)"

lemma binseq_no_rem: "binary_sequence x (Suc n) = (if most_sig_bdig (x - \<Sum>{bool_mult (binary_sequence x k)  1/(2^k) | k. 1 < k \<and> k < n}) > Suc n 
                              then False else True)"
  apply(simp add: binary_remainder_def)
  done

declare binseq_rem [simp del]
declare binseq_no_rem [simp add]

find_theorems "Sum"

(* TODO:
lemma "\<forall>r :: real. 0 < r \<and> r < 1 \<longrightarrow> (\<exists>f :: nat \<Rightarrow> bool. seq_to_real f = r)"
*)


text \<open>
  7.3 Show that \<exists>f s.t. f: (0, 1) => real and f is surjective. f x = tan(\<pi>x - \<pi>/2). ==> |(0, 1)| \<le> |\<real>|
\<close>
definition fitted_tan :: "real \<Rightarrow> real" where
"fitted_tan x = tan (pi*x - pi/2)"

definition fitted_arctan :: "real \<Rightarrow> real" where
"fitted_arctan x = (arctan x + pi/2) / pi"

lemma fitted_arctan: "0 < fitted_arctan y \<and> fitted_arctan y < 1 \<and> fitted_tan (fitted_arctan y) = y"
  unfolding fitted_arctan_def fitted_tan_def
  by (smt (verit) arctan divide_less_eq_1_pos divide_pos_pos field_sum_of_halves nonzero_mult_div_cancel_left times_divide_eq_right)

lemma fitted_reverse [simp]: "\<forall>y. fitted_tan (fitted_arctan y) = y"
  unfolding fitted_arctan_def fitted_tan_def
  by (simp add: arctan)

lemma fitted_surj [simp]: "\<forall>r. \<exists>x. fitted_tan x = r"
  using fitted_reverse by blast
  
lemma "fitted_tan ` {r. 0 < r \<and> r < 1} = UNIV"
  using fitted_arctan fitted_surj image_iff by fastforce


text \<open>
  8. Russel's Paradox
\<close>
(*
In the context of Generalized_Cantor g becomes the characteristic function of sets that are not
members of themselves, i.e. g x = True iff Not (Elem x x).

So, if there was a set R which included all the sets that are not members of themselves then,
Elem R = g

But such R cannot exist as Elem is not surjective, it cannot represent g, by Classic_Cantor.
*)
lemma "Russels's_Paradox": "surj Elem \<Longrightarrow> False"
  apply (rule Classic_Cantor)
  by simp


(*
Possible directions:
  Prove that real numbers and (nat \<Rightarrow> bool)s have the same cardinality

  Using Generalized_Cantor, show Russel's paradox

  Model Turing machines and languages. Show that there are more languages than Turing machines \<longrightarrow>
  hence prove the existence of non-r.e. languages. Derive the Halting problem.
*)

end

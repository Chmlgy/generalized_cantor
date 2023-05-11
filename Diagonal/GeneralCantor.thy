section \<open> Generalized Cantor's Theorem and Instances  \<close>

theory GeneralCantor imports Complex_Main
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
  T x T ---- f ----> Y
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
  7.1 Show that \<exists>f s.t. f: \<real> \<longlongrightarrow> \<P>(\<rat>) and f is injective.
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
  7.2 Show that \<exists>f s.t. f: (nat => bool) => real and f is injective.
\<close>
definition seq_to_real :: "(nat \<Rightarrow> bool) \<Rightarrow> real" where
"seq_to_real f = \<Sum>{1/(2^n) | n. f n = True}"

value "seq_to_real (\<lambda>x. (if x = 1 then True else False))"

lemma "contra_inj_seq_to_real": "\<forall>f h :: (nat \<Rightarrow> bool). f \<noteq> h \<longrightarrow> seq_to_real f \<noteq> seq_to_real h"

lemma "\<exists>f :: (nat \<Rightarrow> bool) \<Rightarrow> real. inj f"


(*
Possible directions:
  Prove that real numbers and (nat \<Rightarrow> bool)s have the same cardinality by Cantor-Schroder-Bernstein

  Using Generalized_Cantor, show Russel's paradox and existence of non-r.e. language
*)
typ real

end

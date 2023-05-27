section \<open> Generalized Cantor's Theorem and Instances\<close>

theory GeneralCantor imports Complex_Main "HOL-Library.Countable" "HOL-Analysis.Analysis"
  "HOL-ZF.HOLZF" "~~/afp-2023-05-17/thys/Universal_Turing_Machine/HaltingProblems_K_H"
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
theorem "Classic_Cantor":
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes surjectivity: "surj f"
  shows "False"
  apply(rule Generalized_Cantor[of f Not])
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
lemma one_elem_to_fixed: "(\<forall>a b :: 'b. a = b) \<longrightarrow> (\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y)"
  by simp

lemma fixed_to_one_elem: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b)"
proof (rule ccontr)
  assume "\<not> ((\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b))"
  hence contra: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<and> (\<exists>a b :: 'b. a \<noteq> b)" by simp
  from contra have fixed_point: "\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y" by simp
  from contra have diff_elem: "\<exists>a b :: 'b. a \<noteq> b" by simp
  then obtain a b where "a \<noteq> (b :: 'b)" by blast
  hence "\<exists> f :: 'b \<Rightarrow> 'b. f = (\<lambda>x. (if x = a then b else a))" by fast
  then obtain f where no_fixed_point: "\<forall>y :: 'b. f y \<noteq> y" by (metis \<open>a \<noteq> (b::'b)\<close>)
  thus "False" using fixed_point no_fixed_point by blast
qed

theorem "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longleftrightarrow> (\<forall>a b :: 'b. a = b)"
proof -
  have forward: "(\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y) \<longrightarrow> (\<forall>a b :: 'b. a = b)" using fixed_to_one_elem by simp
  have backward: "(\<forall>a b :: 'b. a = b) \<longrightarrow> (\<forall>\<alpha> :: 'b \<Rightarrow> 'b. \<exists>y. \<alpha> y = y)" using one_elem_to_fixed by simp
  thus ?thesis using forward backward by metis
qed


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
  7.2 Show that \<exists>f s.t. f: (nat => bool) => real and f is surjective on [0, 1].
       \<Longrightarrow> 2^(\<aleph>_0) \<ge> |[0,1]|
\<close>
(*A function that is surjective on real numbers between 0 and 1: *)
definition seq_to_real :: "(nat \<Rightarrow> bool) \<Rightarrow> real" where
"seq_to_real f = \<Sum>{1/(2^n) | n. f n = True}"

(*Helper definition and functions to prove that the above function is surjective: *)
(*A function that returns the most significant binary digit for a real number between 0 and 1: *)
definition most_sig_bdig :: "real \<Rightarrow> nat" where
"most_sig_bdig x = Min {n. 1/(2^n) < x}" 

definition bool_mult :: "bool \<Rightarrow> real \<Rightarrow> real" where
"bool_mult b x = (if b = False then 0 else x)"

(*A function that expands a real number between 0 and 1 to its binary representation: *)
definition binary_remainder :: "(real \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real set" where
"binary_remainder bs x n = {bool_mult (bs x k)  1/(2^k) | k. 1 < k \<and> k < n}"

lemma [fundef_cong]:
  assumes "x = x'" and "n = n'" and "\<And>k. k < n \<Longrightarrow> bs x k = bs' x k"
  shows "binary_remainder bs x n = binary_remainder bs' x' n'"
  using assms unfolding binary_remainder_def
  by force

fun binary_sequence :: "real \<Rightarrow> nat \<Rightarrow> bool" where
"binary_sequence x 0 = (if most_sig_bdig x > 1 then False else True)" |
binseq_rem: "binary_sequence x (Suc n) =
  (if most_sig_bdig (x - \<Sum>(binary_remainder binary_sequence x n)) > Suc n
   then False else True)"

lemma binseq_no_rem: "binary_sequence x (Suc n) =
  (if most_sig_bdig (x - \<Sum>{bool_mult (binary_sequence x k)  1/(2^k) | k. 1 < k \<and> k < n}) > Suc n
   then False else True)"
  apply(simp add: binary_remainder_def)
  done

declare binseq_rem [simp del]
declare binseq_no_rem [simp add]

(* TODO:
lemma "\<forall>r :: real. 0 < r \<and> r < 1 \<longrightarrow> (\<exists>f :: nat \<Rightarrow> bool. seq_to_real f = r)"
*)


text \<open>
  7.3 Show that \<exists>f s.t. f: (0, 1) => real and f is surjective. f x = tan(\<pi>x - \<pi>/2).
      \<Longrightarrow> |(0, 1)| \<le> |\<real>|
\<close>
definition fitted_tan :: "real \<Rightarrow> real" where
"fitted_tan x = tan (pi*x - pi/2)"

definition fitted_arctan :: "real \<Rightarrow> real" where
"fitted_arctan x = (arctan x + pi/2) / pi"

lemma fitted_arctan: "0 < fitted_arctan y \<and> fitted_arctan y < 1 \<and> fitted_tan (fitted_arctan y) = y"
  unfolding fitted_arctan_def fitted_tan_def
  by (smt (verit) arctan divide_less_eq_1_pos divide_pos_pos field_sum_of_halves
      nonzero_mult_div_cancel_left times_divide_eq_right)

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


text \<open>
  9. Counting argument to show the existence of non-r.e. languages
\<close>
instance action :: countable
  by countable_datatype

theorem "Non-re_Languages":
  assumes surjectivity: "surj TMC_has_num_list_res"
  shows "False"
  apply(rule Abstracted_Cantor[of TMC_has_num_list_res Not nat_list_to_tm tm_to_nat_list])
  apply(auto simp add: surjectivity nat_list_to_tm_is_inv_of_tm_to_nat_list)
  done


text \<open>
  10. Turing Machines and the Halting Problem
\<close>
definition "halts p ns \<equiv> \<exists>Q. \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>Q\<rbrace>"

definition "decides_halting H \<equiv> composable_tm0 H \<and> (\<forall>(p::tprog0) (ns::nat list).
  \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat_list p, ns)>)\<rbrace>
    H
  \<lbrace>\<lambda>tap. \<exists>(k::nat) (n::nat). tap = (Bk \<up> k, <(if halts p ns then 0::nat else 1::nat)>)\<rbrace>)"

lemma not_halts: "\<not> halts p ns \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<up>"
  using halts_def Hoare_unhalt_def reaches_final_def reaches_final_iff by blast

theorem "Halting_Problem":
  assumes "\<exists>dither::tprog0. \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>
                          \<and> \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)\<rbrace> dither \<up>"
  and "\<exists>copy::tprog0. (composable_tm0 copy)
                    \<and> (\<forall>n::nat list. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>)"

  shows "\<nexists>H. decides_halting H"
proof (rule ccontr)
  note [[show_types]]
  assume "\<not> (\<nexists>H::(action \<times> nat) list. decides_halting H)"
  hence "\<exists>H::tprog0. decides_halting H" by simp

  then obtain H::tprog0 where h: "decides_halting H" ..
  from assms(1) obtain dither::tprog0 where d: "\<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>
                                              \<and> \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)\<rbrace> dither \<up>" ..
  from assms(2) obtain copy::tprog0 where c: "composable_tm0 copy
                                            \<and> (\<forall>n::nat list. \<lbrace>\<lambda>tap. tap = ([], <n>)\<rbrace> copy \<lbrace>\<lambda>tap. tap = ([Bk], <(n, n)>)\<rbrace>)" ..

  let ?contra = "copy |+| H |+| dither"
  show "False"
  proof cases
    assume contra_halts: "halts ?contra (tm_to_nat_list ?contra)"

    from c have p1: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> copy
                 \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat_list ?contra, tm_to_nat_list ?contra)>)\<rbrace>" by simp
    from h contra_halts have p2: "\<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat_list ?contra, tm_to_nat_list ?contra)>)\<rbrace>
                                   H
                                  \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)\<rbrace>" unfolding decides_halting_def by presburger
    from d have p3: "\<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)\<rbrace> dither \<up>" by simp

    from c p1 p2 have p1_2: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> copy |+| H \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)\<rbrace>"
      using Hoare_plus_halt by blast
    from c h p1_2 p3 have "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> ?contra \<up>"
      using Hoare_plus_unhalt decides_halting_def seq_tm_composable by blast

    then show ?thesis using contra_halts halts_def Hoare_unhalt_impl_not_Hoare_halt by blast
  next
    assume contra_unhalts: "\<not> halts ?contra (tm_to_nat_list ?contra)"
    hence contra_unhalts_unf: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> ?contra \<up>"
      using halts_def not_halts Hoare_halt_def by blast

    from c have p1: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> copy
                 \<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat_list ?contra, tm_to_nat_list ?contra)>)\<rbrace>" by simp
    from h contra_unhalts have p2: "\<lbrace>\<lambda>tap. tap = ([Bk], <(tm_to_nat_list ?contra, tm_to_nat_list ?contra)>)\<rbrace>
                                     H
                                    \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>" unfolding decides_halting_def by presburger
    from d have p3: "\<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace> dither \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>" by simp

    from c p1 p2 have p1_2: "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> copy |+| H \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>"
      using Hoare_plus_halt by blast
    from c h p1_2 p3 have "\<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list ?contra>)\<rbrace> ?contra \<lbrace>\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)\<rbrace>"
      using Hoare_plus_halt decides_halting_def seq_tm_composable by blast

    then show ?thesis using contra_unhalts_unf Hoare_halt_impl_not_Hoare_unhalt by blast
  qed
qed

(*
  p :: tprog0

  \<forall>p' :: tprog0.
    (p halts on tape <p'> with result b :: bool) 
    \<and> (p' halts on empty tape) \<longleftrightarrow> b

definition "decides_halting p \<equiv> \<forall>p'::tprog0.
  \<lbrace>\<lambda>tap. tap = ([], <tm_to_nat_list p'>)\<rbrace>
    p
  \<lbrace>\<lambda>tap. \<exists>kr lr n. tap = (Bk \<up> kr, <n::nat> @ Bk \<up> lr) \<and> (n=1 \<longleftrightarrow> TMC_has_num_list_res p' [])\<rbrace>"

lemma aux_det: "TMC_yields_num_res p xs n \<Longrightarrow> TMC_yields_num_res p xs n' \<Longrightarrow> n=n'" sorry

find_theorems TMC_yields_num_res
find_theorems "_::tprog0" name: det 

lemma "decides_halting p \<longleftrightarrow> (\<forall>p'. \<exists>n. TMC_yields_num_res p (tm_to_nat_list p') n \<and> (n=1 \<longleftrightarrow> TMC_has_num_list_res p' [] ))"
  unfolding decides_halting_def Hoare_halt_def
  apply auto
  
lemma "\<nexists>p. decides_halting p"
  unfolding decides_halting_def
  find_theorems name: HaltingProblems
*)


end

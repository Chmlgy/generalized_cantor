theory ImpExpressions imports Main
begin

type_synonym vname = "string"
datatype aexp      = N "int" | V "vname" | Plus "aexp" "aexp"
type_synonym val   = "int"
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s        = n" |
"aval (V x) s        = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n)        = N n" |
"asimp_const (V x)        = V x" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N(n1+n2) |
    (b1,b2)      \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
  apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a       = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i)       = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2         = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
  apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n)        = N n" |
"asimp (V x)        = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
  apply(auto simp add: aval_plus)
  done

(*Exercises 3.1-6*)
fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N i)                = True" |
"optimal (V i)                = True" |
"optimal (Plus (N n1) (N n2)) = False" |
"optimal (Plus a1 a2)         = (optimal a1 \<and> optimal a2)"

lemma "optimal (asimp_const a)"
  apply(induction a)
  apply(auto split: aexp.split)
  done

fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"full_plus (N i) (N j)          = N (i + j)" |
"full_plus (Plus p (N a)) (N b) = Plus p (N (a + b))" |
"full_plus (N b) (Plus p (N a)) = Plus p (N (a + b))" |
"full_plus (Plus (N a) p) (N b) = Plus p (N (a + b))" |
"full_plus (N b) (Plus (N a) p) = Plus p (N (a + b))" |
"full_plus p (N i)              = (if i = 0 then p else Plus p (N i))" |
"full_plus (N i) p              = (if i = 0 then p else Plus p (N i))" |
"full_plus p q                  = (Plus p q)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N i)        = N i" |
"full_asimp (V i)        = V i" |
"full_asimp (Plus a1 a2) = full_plus (full_asimp a1) (full_asimp a2)"

lemma [simp]: "aval (full_plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: full_plus.induct)
  apply(auto)
  done

theorem full_asimp_preserve: "aval (full_asimp a) s = aval a s"
  apply(induction a)
  apply(auto)
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x e (N i)        = N i" |
"subst x e (V i)        = (if x = i then e else V i)" |
"subst x e (Plus a1 a2) = Plus (subst x e a1) (subst x e a2)"

lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
  apply(auto)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction a1)
  apply(auto)
  done

datatype aexpm = Nm "int" | Vm "vname" | Plusm "aexpm" "aexpm" | Times "aexpm" "aexpm"

fun avalm :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
"avalm (Nm n) s        = n" |
"avalm (Vm x) s        = s x" |
"avalm (Plusm a1 a2) s = avalm a1 s + avalm a2 s" |
"avalm (Times a1 a2) s = avalm a1 s * avalm a2 s"

fun plusm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"plusm (Nm i1) (Nm i2) = Nm (i1 + i2)" |
"plusm (Nm i) a        = (if i = 0 then a else Plusm (Nm i) a)" |
"plusm a (Nm i)        = (if i = 0 then a else Plusm a (Nm i))" |
"plusm a1 a2           = Plusm a1 a2"

fun mult :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"mult (Nm i1) (Nm i2) = Nm (i1 * i2)" |
"mult (Nm i) a        = (if i = 0 then (Nm 0) else if i = 1 then a else Times (Nm i) a)" |
"mult a (Nm i)        = (if i = 0 then (Nm 0) else if i = 1 then a else Times a (Nm i))" |
"mult a1 a2           = Times a1 a2"

fun asimpm :: "aexpm \<Rightarrow> aexpm" where
"asimpm (Nm n)        = Nm n" |
"asimpm (Vm x)        = Vm x" |
"asimpm (Plusm a1 a2) = plusm (asimpm a1) (asimpm a2)" |
"asimpm (Times a1 a2) = mult (asimpm a1) (asimpm a2)"

lemma [simp]: "avalm (plusm p q) s = avalm p s + avalm q s"
  apply(induction p q rule: plusm.induct)
  apply(auto)
  done
  
lemma [simp]: "avalm (mult p q) s = avalm p s * avalm q s"
  apply(induction p q rule: mult.induct)
  apply(auto)
  done

theorem "avalm (asimpm p) s = avalm p s"
  apply(induction p)
  apply(auto)
  done

(*TODO: define div with options*)
datatype aexp2 = N2 "int" | V2 "vname" | Plus2 "aexp2" "aexp2" | PlusPlus2 "vname"
  | Times2 "aexp2" "aexp2"

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val * state)" where
"aval2 (N2 i) s         = (i, s)" |
"aval2 (V2 i) s         = (s i, s)" |
"aval2 (PlusPlus2 i) s  = (s i, s(i := s i + 1))" |
"aval2 (Plus2 a1 a2) s  = (let p = aval2 a1 s;
                          q = aval2 a2 s in (fst p + fst q, (\<lambda>x. (snd p) x + (snd q) x - s x)))" |
"aval2 (Times2 a1 a2) s = (let p = aval2 a1 s;
                          q = aval2 a2 s in (fst p * fst q, (\<lambda>x. (snd p) x + (snd q) x - s x)))"

datatype lexp = Nl "int" | Vl "vname" | Plusl "lexp" "lexp" | LET "vname" "lexp" "lexp"

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl i) s        = i" |
"lval (Vl i) s        = s i" |
"lval (Plusl l1 l2) s = lval l1 s + lval l2 s" |
"lval (LET x l1 l2) s = lval l2 (s(x := lval l1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl i)        = N i" |
"inline (Vl i)        = V i" |
"inline (Plusl l1 l2) = Plus (inline l1) (inline l2)" |
"inline (LET x l1 l2) = subst x (inline l1) (inline l2)"

theorem "lval l = aval (inline l)"
  apply(induction l)
  apply(auto)
  done
(*End of exercises*)

datatype bexp = Bc "bool" | Not "bexp" | And "bexp" "bexp" | Less "aexp" "aexp"

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s       = v" |
"bval (Not b) s      = (\<not> bval b s)" |
"bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True)  = Bc False" |
"not (Bc False) = Bc True" |
"not b          = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b  = b" |
"and b (Bc True)  = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2        = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc (n1 < n2)" |
"less a1 a2         = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v)       = Bc v" |
"bsimp (Not b)      = not (bsimp b)" |
"bsimp (And b1 b2)  = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

(*Exercises 3.7-9*)
definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply(auto simp add: Eq_def)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply(auto simp add: Le_def)
  done

datatype ifexp = Bc2 "bool" | If "ifexp" "ifexp" "ifexp" | Less2 "aexp" "aexp"

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s       = v" |
"ifval (If i1 i2 i3) s = (if ifval i1 s then ifval i2 s else ifval i3 s)" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v)       = Bc2 v" |
"b2ifexp (Not b)      = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And b1 b2)  = If (b2ifexp b1) (If (b2ifexp b2) (Bc2 True) (Bc2 False)) (Bc2 False)" |
"b2ifexp (Less a1 a2) = Less2 a1 a2"

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b1 b2 = Not (And (Not b1) (Not b2))"

definition Implies :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Implies b1 b2 = Or (Not b1) b2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v)       = Bc v" |
"if2bexp (If i1 i2 i3) = And (Implies (if2bexp i1) (if2bexp i2)) (Implies (Not (if2bexp i1)) (if2bexp i3))" |
"if2bexp (Less2 a1 a2) = Less a1 a2"

lemma "bval b = ifval (b2ifexp b)"
  apply(induction b)
  apply(auto)
  done

lemma "ifval i = bval (if2bexp i)"
  apply(induction i)
  apply(auto simp add: Or_def Implies_def)
  done

datatype pbexp = VAR "vname" | NEG "pbexp" | AND "pbexp" "pbexp" | OR "pbexp" "pbexp"

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s     = s x" |
"pbval (NEG b) s     = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s  = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR v)     = True" |
"is_nnf (AND p1 p2) = (is_nnf p1 \<and> is_nnf p2)" |
"is_nnf (OR p1 p2)  = (is_nnf p1 \<and> is_nnf p2)" |
"is_nnf (NEG p1)    =
  (case p1 of
    (VAR v) \<Rightarrow> True |
    _       \<Rightarrow> False)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR v)         = VAR v" |
"nnf (NEG (VAR p))   = (NEG (VAR p))" |
"nnf (NEG (NEG p))   = nnf p" |
"nnf (NEG (AND p q)) = OR (nnf (NEG p)) (nnf (NEG q))" |
"nnf (NEG (OR p q))  = AND (nnf (NEG p)) (nnf (NEG q))" |
"nnf (AND p1 p2)     = AND (nnf p1) (nnf p2)" |
"nnf (OR p1 p2)      = OR (nnf p1) (nnf p2)"

theorem "pbval (nnf b) s = pbval b s"
  apply(induction b rule: nnf.induct)
  apply(auto)
  done

theorem "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
  apply(auto)
  done
(*TODO: DNF form*)
(*End of exercises*)

datatype instr = LOADI "val" | LOAD "vname" | ADD
type_synonym stack = "val list"

(*Exercises 3.10-12*)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD x) s stk  = Some ((s x) # stk)" |
"exec1 ADD _ stk       =
  (case stk of
    []             \<Rightarrow> None |
    [i]            \<Rightarrow> None |
    (i # j # stk2) \<Rightarrow> Some ((i + j) # stk2))"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk       = Some stk" |
"exec (i # is) s stk =
  (case (exec1 i s stk) of
    None      \<Rightarrow> None |
    Some stk2 \<Rightarrow> exec is s stk2)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n)        = [LOADI n]" |
"comp (V x)        = [LOAD x]" |
"comp (Plus a1 a2) = comp a1 @ comp a2 @ [ADD]"

lemma [simp]: "(exec i1 s stk) = Some stk2 \<Longrightarrow> exec (i1 @ i2) s stk = exec i2 s stk2"
  apply(induction i1 arbitrary: stk)
  apply(auto split: option.split)
  done

lemma "exec (comp a) s stk = Some (aval a s # stk)"
  apply(induction a arbitrary: stk)
  apply(auto)
  done

type_synonym reg = "nat"
datatype rinstr = LDI "int" "reg" | LD "vname" "reg" | ADD "reg" "reg"

fun rexec1 :: "rinstr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec1 (LDI i r) _ lookup   = lookup(r := i)" |
"rexec1 (LD x r) s lookup    = lookup(r := (s x))" |
"rexec1 (ADD r1 r2) _ lookup = lookup(r1 := (lookup r1 + lookup r2))"

fun rexec :: "rinstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec [] _ lookup         = lookup" |
"rexec (ri # ris) s lookup = rexec ris s (rexec1 ri s lookup)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
"rcomp (N n) r        = [LDI n r]" |
"rcomp (V x) r        = [LD x r]" |
"rcomp (Plus a1 a2) r = rcomp a1 r @ rcomp a2 (r+1) @ [ADD r (r+1)]"

lemma [simp]: "rexec (ris1 @ ris2) s lookup = rexec ris2 s (rexec ris1 s lookup)"
  apply(induction ris1 arbitrary: lookup)
  apply(auto)
  done

lemma register_contamination: "\<lbrakk>r < q\<rbrakk> \<Longrightarrow> rexec (rcomp a q) s lookup r = lookup r"
  apply(induction a arbitrary: lookup r q)
  apply(auto)
  done

lemma "rexec (rcomp a r) s lookup r = aval a s"
  apply(induction a arbitrary: lookup r)
  apply(auto simp add: register_contamination)
  done
(*TODO: 3.12*)
(*End of exercises*)

end

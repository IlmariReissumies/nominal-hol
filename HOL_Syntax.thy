theory HOL_Syntax2
  imports Nominal2
begin

datatype ty =
  TVar string
| TApp string "ty list"

primrec
  ty_inst::"ty\<Rightarrow>string\<Rightarrow>ty\<Rightarrow>ty"
where
  "ty_inst (TVar s) s' t = (if s = s' then t else TVar s)"
| "ty_inst (TApp s tys) s' t = TApp s (map (\<lambda> ty. ty_inst ty s' t) tys)"

atom_decl name

instantiation ty :: pt
begin
definition
  "p \<bullet> (t::ty) = t"

instance
by standard (simp_all add: permute_ty_def)
end

instantiation ty :: fs
begin
instance
by standard (simp add: supp_def permute_ty_def)
end

instantiation ty :: pure
begin
instance
by standard (simp add: permute_ty_def)
end

nominal_datatype lam =
  VAR "name" ty
| CON "string" ty
| APP "lam" "lam"
| ABS x::"name" t::"ty" l::"lam"  binds x in l ("LAM [_ : _]. _" [100, 100, 100] 100)

nominal_function
  lam_inst :: "lam \<Rightarrow> string \<Rightarrow> ty \<Rightarrow> lam"
where
  "lam_inst (VAR v t') s t = VAR v (ty_inst t' s t)"
| "lam_inst (CON c t') s t = CON c (ty_inst t' s t)"
| "lam_inst (APP x y) s t = APP (lam_inst x s t) (lam_inst y s t)"
| "lam_inst (ABS x xt y) s t = ABS x xt (lam_inst y s t)"
apply(simp add: eqvt_def lam_inst_graph_aux_def)
apply(rule TrueI)
apply(rule_tac y="fst x" in lam.exhaust)
apply(auto)[4]
apply(simp_all add: fresh_Pair Abs_fresh_iff)
apply force
apply clarify
apply(simp only: eqvt_at_def)
apply(drule_tac x="(x \<leftrightarrow> c)" in spec)
apply(drule_tac x="(xa \<leftrightarrow> c)" in spec)
apply(drule_tac x="c" in spec)
apply auto
apply perm_simp
apply simp
done

(* no_notation (ASCII) Set.member ("op :") *)

abbreviation
Fun :: "ty \<Rightarrow> ty \<Rightarrow> ty" (infix "\<rightarrow>" 91)
where 
"Fun x y \<equiv> TApp ''fun'' [x,y]"

inductive has_type :: "lam \<Rightarrow> ty \<Rightarrow> bool" (infix ":" 90)
where
  has_type_Var: "(VAR n ty) : ty"
| has_type_Con: "(CON c ty) : ty"
| has_type_App: "\<lbrakk>s : dty \<rightarrow> rty; t : dty\<rbrakk> \<Longrightarrow> APP s t : rty"
| has_type_Abs: "t : rty \<Longrightarrow> ABS n dty t : dty \<rightarrow> rty"

equivariance has_type

lemmas has_type_intros = has_type_Var has_type_Con has_type_App has_type_Abs

definition well_typed :: "lam \<Rightarrow> bool"
where "well_typed x = (\<exists> ty::ty. x : ty)" 

fun
  codomain :: "ty \<Rightarrow> ty"
where
  "codomain t = (case t of dt \<rightarrow> rt \<Rightarrow> rt)"

lemma unpermute_pure[simp]:
fixes x :: "'a::pure"
shows "unpermute p x = x"
by(simp add: unpermute_def permute_pure)

lemma
fixes q::"'a::pt"
assumes "(x \<leftrightarrow> a) \<bullet> q = t"
shows "q = (a \<leftrightarrow> x) \<bullet> t"
using assms permute_flip_cancel2 by auto

nominal_function
  type_of :: "lam \<Rightarrow> ty"
where
  "type_of (VAR v t) = t"
| "type_of (CON c t) = t"
| "type_of (APP x y) = codomain(type_of x)"
| "type_of (ABS x t y) = t \<rightarrow> (type_of y)"
apply(simp add: eqvt_def type_of_graph_aux_def)
apply(subst unpermute_pure)+
apply force
apply(rule TrueI)
apply(rule_tac y="x" in lam.exhaust)
apply(auto)[4]
apply(simp_all add: fresh_Pair Abs_fresh_iff)[9]
using [[simproc del: alpha_lst]]
apply clarsimp
apply(erule_tac c="()" in Abs_lst1_fcb2)
apply(simp add: pure_fresh)
apply(simp add: fresh_star_def pure_fresh)
by(simp_all only: eqvt_at_def)

nominal_termination (eqvt) by(lexicographic_order)

lemma well_typed_app_dest[dest]:
  assumes "well_typed (APP x y)"
  shows "well_typed x"
  and "well_typed y"
proof -
  from assms obtain t::ty where "APP x y : t"
    by(auto simp add: well_typed_def)
  thus "well_typed x" and "well_typed y"
    by(cases rule: has_type.cases,auto simp add: well_typed_def)+
qed

lemma well_typed_app_rator_fun_type:
  assumes "well_typed (APP x y)"
  shows "\<exists> ty ty'. x : ty \<rightarrow> ty'"
proof -
  from assms obtain t::ty where "APP x y : t"
    by(auto simp add: well_typed_def)
  thus ?thesis
    by(cases rule: has_type.cases,auto simp add: well_typed_def)
qed

lemma well_typed_lam_dest[dest]:
  assumes "well_typed (ABS x t y)"
  shows "well_typed y"
proof -
  from assms obtain ty::ty where "ABS x t y : ty"
    by(auto simp add: well_typed_def)
  thus "well_typed y"
    apply(cases rule: has_type.cases)
    apply(drule sym)
    apply(auto simp add: well_typed_def)
    apply(rule_tac x="(x,y,ta,rty,ty,n)" and ?'a="name" in obtain_fresh)
    apply(drule_tac p="(x\<leftrightarrow>a) + (n\<leftrightarrow>a)" in has_type.eqvt)
    by(auto simp add: permute_pure)
qed

lemma has_type_well_typed[intro]:
  fixes ty::ty
  assumes "tm : ty"
  shows "well_typed tm"
using assms
by(induct rule: has_type.induct) (auto simp add: well_typed_def intro: has_type_intros)

lemma has_type_unique:
  fixes ty ty'::ty
  assumes "x : ty"
  and "x : ty'"
  shows "ty = ty'"
using assms
proof(nominal_induct x arbitrary: ty ty' rule: lam.strong_induct)
  case (VAR n ty) thus ?case
    by(cases rule: has_type.cases) (cases rule: has_type.cases,auto)
next
  case (CON c ty) thus ?case
    by(cases rule: has_type.cases) (cases rule: has_type.cases,auto)
next
  case (APP x y ty ty')
  from `APP x y : ty` show ?case
  proof(cases rule: has_type.cases)
    case(has_type_App dty)
    note xty = this
    from `APP x y : ty'` show ?thesis
    proof(cases rule: has_type.cases)
      case(has_type_App dty')
      note xty' = this
      show ?thesis
        using xty xty'
        by(auto dest: APP(1))
    qed
  qed
next
  case (ABS n ty x ty' ty'')
  from `LAM [n : ty]. x : ty'` show ?case
  proof(cases rule: has_type.cases)
    case(has_type_Abs y rty n')
    note xty = this
    from `LAM [n : ty]. x : ty''` show ?thesis
    proof(cases rule: has_type.cases)
      case(has_type_Abs y' rty' n'')
      note xty' = this
      show ?thesis
        using xty xty'
        apply(drule_tac sym[where t="[[atom n']]lst. y"])
        apply(drule_tac sym[where t="[[atom n'']]lst. y'"])
        apply(rule_tac x="(x,y,y',n,n',n'')" and ?'a="name" in obtain_fresh)
        apply(drule_tac p="(n \<leftrightarrow> a)+(n' \<leftrightarrow> a)" in has_type.eqvt)
        apply(drule_tac p="(n \<leftrightarrow> a)+(n'' \<leftrightarrow> a)" in has_type.eqvt)        
        by(auto dest: ABS(1) simp add: permute_pure)
    qed
  qed
qed

lemma app_ret_type_unique:
  fixes ty ty' ty'' :: ty
  assumes "APP x y : ty''"
  and "x : ty \<rightarrow> ty'"
  shows "APP x y : ty'"
using assms
proof(cases rule: has_type.cases)
  case(has_type_App dty)
  with `x : ty \<rightarrow> ty'` have
  "dty \<rightarrow> ty'' = ty \<rightarrow> ty'"
    by(drule_tac has_type_unique)
  thus ?thesis using `APP x y : ty''`
    by simp
qed

lemma well_typed_compute_type:
  shows "well_typed tm = tm : type_of tm"
apply(nominal_induct tm rule: lam.strong_induct)
apply(auto intro: has_type_intros dest: well_typed_app_dest)
apply(frule_tac well_typed_app_rator_fun_type)
apply clarify
apply(drule_tac has_type_unique, assumption)
by(auto simp add: well_typed_def intro: app_ret_type_unique)

nominal_function
  lam_subst :: "lam \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> lam \<Rightarrow> lam" ("_ [_:_ ::= _]" [90, 90, 90] 90)
where
  "(VAR v t)[n:t'::=l] = (if v = n \<and> t = t' then l else (VAR v t))"
| "(CON c t)[n:t'::=l] = CON c t"
| "(APP x y)[n:t'::=l] = APP (x[n:t'::=l]) (y[n:t'::=l])"
| "atom x \<sharp> (n,l) \<Longrightarrow> (ABS x t y)[n:t'::=l] = ABS x t (y[n:t'::=l])"
apply(simp add: eqvt_def lam_subst_graph_aux_def)
apply(rule TrueI)
using [[simproc del: alpha_lst]]
apply clarify
apply(rule_tac y="a" and c="(aa,b)" in lam.strong_exhaust)
apply(auto simp add: fresh_star_def)[13]
apply(simp add: fresh_star_def fresh_Pair_elim)
apply(erule conjE)+
apply (erule_tac c="(na,la)" in Abs_lst1_fcb2)
apply(simp_all add: Abs_fresh_iff)
apply(simp add: fresh_star_def fresh_Pair)
apply(simp only: eqvt_at_def)
apply(perm_simp)
apply(simp)
apply(simp add: fresh_star_Pair perm_supp_eq)
apply(simp only: eqvt_at_def)
apply(perm_simp)
apply(simp)
apply(simp add: fresh_star_Pair perm_supp_eq)
done

nominal_termination (eqvt) by(lexicographic_order)

lemma subst_pres_type:
  fixes ty :: ty
  assumes "type_of t = ty"
  shows "type_of(x[n:ty ::= t]) = type_of(x)"
using assms
by(nominal_induct x avoiding: n t arbitrary: ty rule: lam.strong_induct) auto

end
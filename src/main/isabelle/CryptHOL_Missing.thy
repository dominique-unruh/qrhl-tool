theory CryptHOL_Missing
  imports CryptHOL.Misc_CryptHOL
begin

instantiation nlist :: (plus,len0) plus begin
lift_definition plus_nlist :: "('a,'b) nlist \<Rightarrow> ('a,'b) nlist \<Rightarrow> ('a,'b) nlist" is "List.map2 (+)"
  unfolding nlists_alt_def by auto
instance by standard
end

instantiation nlist :: (minus,len0) minus begin
lift_definition minus_nlist :: "('a,'b) nlist \<Rightarrow> ('a,'b) nlist \<Rightarrow> ('a,'b) nlist" is "List.map2 (-)"
  unfolding nlists_alt_def by auto
instance by standard
end

instantiation nlist :: (uminus,len0) uminus begin
lift_definition uminus_nlist :: "('a,'b) nlist \<Rightarrow> ('a,'b) nlist" is "List.map uminus"
  unfolding nlists_alt_def by auto
instance by standard
end

instantiation nlist :: (zero,len0) zero begin
lift_definition zero_nlist :: "('a,'b) nlist" is "replicate LENGTH('b) 0"
  by simp
instance by standard
end

instantiation nlist :: (monoid_add,len0) semigroup_add begin
instance
  apply (intro_classes, transfer)
  unfolding zip_map1 zip_map2 map_map zip_assoc o_def case_prod_unfold
  apply simp using Groups.add_ac(1) by blast 
end

instantiation nlist :: (monoid_add,len0) monoid_add begin
instance
proof (intro_classes; transfer)
  fix a :: "'a list"
  assume "a : nlists UNIV LENGTH('b)"
  then have len_a: "length a = LENGTH('b)"
    using in_nlists_UNIV by blast
  then show "map2 (+) (replicate LENGTH('b) 0) a = a"
    apply (induction ("LENGTH('b)") arbitrary: a)
    apply simp apply auto
    by (smt add.left_neutral length_Suc_conv list.map(2) split_conv zip_Cons_Cons)
  from len_a show "map2 (+) a (replicate LENGTH('b) 0) = a"
    apply (induction ("LENGTH('b)") arbitrary: a)
    apply simp apply auto
    by (smt add.right_neutral length_Suc_conv list.map(2) split_conv zip_Cons_Cons)
qed
end

instantiation nlist :: (group_add,len0) group_add begin
instance
proof (intro_classes; transfer)
  fix a :: "'a list"
  assume "a : nlists UNIV LENGTH('b)"
  then have len_a: "length a = LENGTH('b)"
    using in_nlists_UNIV by blast
  then show "map2 (+) (map uminus a) a = replicate LENGTH('b) 0"
  proof (induction ("LENGTH('b)") arbitrary: a)
    case 0 then show ?case by auto
  next
    case (Suc n)
    from Suc.prems obtain a1 a2 where "a = a1#a2"
      by (meson length_Suc_conv)
    with Suc show ?case by auto
  qed
  fix b :: "'a list"
  assume "b \<in> nlists UNIV LENGTH('b)"
  then have len_b: "length b = LENGTH('b)"
    using in_nlists_UNIV by blast
  with len_a have "length a = length b" by simp
  then show "map2 (+) a (map uminus b) = map2 (-) a b"
    apply (induction a b rule:list_induct2)
    by auto
qed
end
(* 
instantiation nlist :: ("value",len0) "value" begin
definition "embedding'_nlist == (fst embedding' o (Rep_nlist::('a,'b) nlist \<Rightarrow> _), snd (embedding'::'a list universe_embedding))"
instance 
  apply (rule OFCLASS_value_typedef[OF embedding'_nlist_def])
  by (rule Rep_nlist_inject)
end *)

(*
instantiation vec :: ("value","{value,finite}") "value" begin
definition "embedding'_vec == (fst embedding' o (vec_nth::('a,'b) vec \<Rightarrow> _), snd (embedding'::('b\<Rightarrow>'a) universe_embedding))"
instance 
  apply (rule OFCLASS_value_typedef[OF embedding'_vec_def])
  by (rule vec_nth_inject)
end

instantiation blinfun :: ("{real_normed_vector,value}","{real_normed_vector,value}") "value" begin
definition "embedding'_blinfun == (fst embedding' o (blinfun_apply::('a,'b) blinfun \<Rightarrow> _), snd (embedding'::('a\<Rightarrow>'b) universe_embedding))"
instance 
  apply (rule OFCLASS_value_typedef[OF embedding'_blinfun_def])
  by (rule blinfun_apply_inject)
end

instantiation bcontfun :: ("{topological_space,value}","{metric_space,value}") "value" begin
definition "embedding'_bcontfun == (fst embedding' o (apply_bcontfun::('a,'b) bcontfun \<Rightarrow> _), snd (embedding'::('a\<Rightarrow>'b) universe_embedding))"
instance 
  apply (rule OFCLASS_value_typedef[OF embedding'_bcontfun_def])
  by (rule apply_bcontfun_inject)
end
*)

end

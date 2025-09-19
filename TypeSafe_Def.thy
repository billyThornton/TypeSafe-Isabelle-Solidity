section\<open>Defining the properties of typesafe environments in Isabelle-Solidity\<close>
theory TypeSafe_Def
  imports TypeSafe_Memory TypeSafe_Storage

begin

lemma frd:
  assumes "(\<not>LSubPrefL2 destl'  destl) \<and> \<not>LSubPrefL2 destl  destl' "
  shows  "(\<forall>l l'. TypedStoSubPref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
          \<and> cps2mTypeCompatible t t'
          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
          \<and> MCon t' v' destl' \<longrightarrow> MCon t' v'' destl'" using assms 
proof (induction t' arbitrary:destl' t)
  case (MTArray x1 t')
  show ?case 
  proof intros
    assume " (\<forall>l l'. TypedStoSubPref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    cps2mTypeCompatible t (MTArray x1 t') \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> MCon (MTArray x1 t') v' destl'"
    then have a10:"(\<forall>l l'. TypedStoSubPref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
      and a20:"cps2mTypeCompatible t (MTArray x1 t')"
      and a30:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      and a40:"MCon (MTArray x1 t') v' destl'" by blast+
    show "MCon (MTArray x1 t') v'' destl'"
    proof(cases "x1>0")
      case True
      have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t' of MTValue typ \<Rightarrow> MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v'' loc2 | MTValue Types \<Rightarrow> False)" 
      proof (intros)
        fix i assume iLess:"i<x1"
        then show " case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t' of MTValue typ \<Rightarrow> MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v'' loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases t')
          case mtr:(MTArray x11 x12)
          then obtain t''' where tdef:"t = STArray x1 (STArray x11 t''')" using a20 mtr cps2mTypeCompatible.simps True 
            by (metis STypes.exhaust)
          then have a45:"cps2mTypeCompatible (STArray x11 t''') (MTArray x11 x12)" using a20 by (simp add: mtr)

          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedStoSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x11 t''') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
                      cps2mTypeCompatible (STArray x11 t''') (MTArray x11 x12) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') 
                      \<and> MCon (MTArray x11 x12) v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                      MCon (MTArray x11 x12) v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
            using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(STArray x11 t''')"] b100 mtr by blast
          have a55:"\<forall>l l'. TypedStoSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x11 t''') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" 
            using a10 stoMoreSpecificTypedSubPref[of destl' x1 "(STArray x11 t''')" v'] iLess using tdef by blast 
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 a30 by blast
          then show ?thesis 
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess a40 by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then show ?thesis using a40 iLess mtr Some by auto
            next
              case (MPointer x2')
              then have x2'def:"x2' = (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a55 Some 
                using iLess TypedStoSubPref.simps(2) a10 tdef by blast
              have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t' of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t' v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v' loc2 | MTValue Types \<Rightarrow> False)" 
                using  MCon.simps(2)[of x1 t' v' destl']
                using a40 by auto
              then have "MCon t' v' (x2')" using a40 iLess Some mtr MPointer tdef MCon.simps(2)[of x1 t' v' destl'] True by fastforce
              then have "MCon t' v'' x2'" using a50 b100 a55 a30 a45 tdef  x2'def mtr by blast
              then show ?thesis  using Some MPointer mtr a60 by auto
            qed
          qed
        next
          case (MTValue x2)
          then have  tdef:"t = STArray x1 (STValue x2)" using a20 cps2mTypeCompatible.simps True 
            by (metis STypes.exhaust)
          then have a45:"cps2mTypeCompatible (STValue x2) (MTValue x2)" using a20 by (simp add: MTValue)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedStoSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STValue x2) 
                    \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) 
                    \<and> cps2mTypeCompatible (STValue x2) (MTValue x2) 
                    \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') 
                      \<and> MCon (MTValue x2) v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                      MCon (MTValue x2) v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100  using MTValue by force
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 a30 by simp
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using iLess a40 by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then have "MCon t' v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a40 iLess Some MTValue by auto
              then have "MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a50 b100 a60 a30 Some MValue MTValue by auto
              then show ?thesis using Some MValue MTValue a60 by auto
            next
              case (MPointer x2')
              then show ?thesis using a40 iLess MTValue Some by auto
            qed

          qed
        qed
      qed
      moreover have "(\<exists>p. accessStore destl' v'' = Some (MPointer p)) \<or> accessStore destl' v'' = None" 
        using MTArray.prems True a10 a20 a30 a40 by force
      ultimately show ?thesis using MCon.simps(2)[of x1 t' v'' destl']
        by (simp add: True)
    next
      case False
      then show ?thesis using a40 by simp
    qed
  qed
next
  case (MTValue x)
  show ?case 
  proof intros
    assume *:"(\<forall>l l'. TypedStoSubPref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    cps2mTypeCompatible t (MTValue x) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> MCon (MTValue x) v' destl'"
    then have "accessStore destl' v' = accessStore destl' v''" using MTValue by simp
    then show "MCon (MTValue x) v'' destl'"  using * by simp
  qed
qed






subsection \<open>Ensuring unique locations\<close>
  (*
Checks a finite map (specifically denvalue) to ensure that the locations are all unique.
The number of unique store locations must equal the number of unique variable names.
*)
definition unique_locations :: "(String.literal, Type \<times> Denvalue) fmap \<Rightarrow> bool" where
  "unique_locations denval = (\<forall>x y. x |\<in>| fmran denval \<and> y |\<in>| fmran denval \<and> snd x = snd y \<longrightarrow> x = y)"


text \<open>Shows that if an enironement has unique locations and two elements are chosen from the denvalue
of which their locations are the same then they must be the same element.
This ensure that no duplicate variables with the same location can exist.\<close>
lemma uniqueLocs:
  assumes "unique_locations (denvalue ev)"
    and "x |\<in>| fmran (denvalue ev)"
    and "y |\<in>| fmran (denvalue ev)"
    and "snd x = snd y"
  shows "x = y" using assms unique_locations_def by blast


subsection \<open>Stack/CD/MEM locations are less then the head of the CD/MEM\<close>
definition lessThanTopLocs :: "'a Store \<Rightarrow> bool" where            
  "lessThanTopLocs st = ((\<forall>tloc loc. tloc \<ge> (toploc st) \<and>  LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc st = None)
                          \<and> (\<forall>loc y. accessStore loc st = Some y \<longrightarrow> (\<exists>tloc. tloc<(toploc st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"

subsubsection \<open>Pushing to the stack maintains stackLocations\<close>

lemma stackPushToplocSafe:
  assumes "lessThanTopLocs k"
    and "k' = push p k"
  shows "lessThanTopLocs k'" unfolding lessThanTopLocs_def
proof(intros)
  fix tloc loc
  assume **:"toploc k' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  have a120:"toploc k<toploc k'" using assms by (simp add:push_def allocate_def updateStore_def accessStore_def)
  have a125:"tloc \<noteq> toploc k" using "**" a120 by auto
  then have a126:"(ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k))" 
    by (metis Read_Show_nat'_id)
  have a130:"\<forall>tloc loc. toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def 
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have a150:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) k = None" using a130 a120 ** 
    by (metis LSubPrefL2_def dual_order.strict_trans1 nless_le)
  then show "accessStore loc k' = None" 
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)")
    case True
    then show ?thesis using acces a150 a126 by simp
  next
    case False
    then show ?thesis using acces a150 a126  ShowLNatDot
      by (metis "**" LSubPrefL2_def a120 a130 hash_inequality hash_int_prefix hash_suffixes_associative nat_less_le order_less_le_trans)
  qed
next 
  fix loc y 
  assume *:"accessStore loc k' = Some y"
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def 
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have " \<exists>tloc<toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k))")
    case True
    have a10:"toploc k < toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    have "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k))" using True LSubPrefL2_def by simp
    have "\<forall>l. l\<noteq>(ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) \<longrightarrow>  \<not>(LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc k)) l)" using ShowLNatDot unfolding LSubPrefL2_def hash_def 
      using subPrefCannotBeInt by auto
    then show ?thesis using True a10 assms 
      using LSubPrefL2_def by auto
  next
    case False
    have "((\<forall>tloc loc. toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None) 
          \<and> (\<forall>loc y. accessStore loc k = Some y \<longrightarrow> (\<exists>tloc<toploc k. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))" 
      using assms lessThanTopLocs_def[of k]  by blast
    then obtain tloc where  tlocdef:"tloc < toploc k \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using False * acces by metis
    moreover have "toploc k < toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    ultimately show ?thesis using assms lessThanTopLocs_def[of k] * tlocdef 
      using order.strict_trans by auto
  qed
  then show "\<exists>tloc<toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" by simp
qed

lemma lessThanSome_imps_Locs:
  assumes "lessThanTopLocs (memory st)"
    and "accessStore p' (memory st) = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < toploc (memory st)"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t x) (memory st) = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < toploc (memory st)" using a10 a20 
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < toploc (memory st)" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i)" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i) (memory st) = Some y" using assms(2) by simp
  have "x < toploc (memory st)" using a10 a20 
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then show ?thesis by blast
qed

lemma lessThanSome_imps_Locs2:
  assumes "lessThanTopLocs (memory st)"
    and " accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st) = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < toploc (memory st)"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st) = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < toploc (memory st)" using a10 a20 
    by (metis LSubPrefL2_def True assms(1) lessThanSome_imps_Locs)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < toploc (memory st)" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i' where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i')" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st) = Some y" using assms(2) by simp
  have "x < toploc (memory st)" using a10 a20 
    by (metis LSubPrefL2_def assms(1) hash_suffixes_associative lessThanSome_imps_Locs)
  then show ?thesis by blast
qed

lemma TS_imps_InDenLessStack2:
assumes "MCon tp1 (memory st) stl1"
  and "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
  and "(\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None)"
  and "(\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
  and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<longrightarrow> accessStore locs (memory st') = accessStore locs (memory st)"
  and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l"
  and "MCon tp2 (memory st') stl2"
shows "\<not> TypedMemSubPrefPtrs (memory st') x11 x12 stl2 stl1" 
proof(cases x12)
  case (MTArray x11' x12')
  have "\<not> TypedMemSubPrefPtrs (memory st') x11 (MTArray x11' x12') stl2 stl1" unfolding TypedMemSubPrefPtrs.simps
  proof
    assume *:"\<exists>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs (memory st') x11' x12' l stl1)"
    then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs (memory st') x11' x12' l stl1)" by blast
    then have lneq:"l \<noteq> stl1" using assms(1,2,4,5,6) 
      by (metis MCon_imps_Some assms(3) lessThanSome_imps_Locs2 lessThanTopLocs_def less_irrefl_nat)
    then have ldef:"l = (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using assms idef 
      by (metis LSubPrefL2_def hash_suffixes_associative)
    then have lsubloc:"LSubPrefL2  l  (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))" using assms
      using LSubPrefL2_def hash_suffixes_associative 
      by metis
    have lneq2:"\<forall>i<x11'. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" 
      by (smt (verit, ccfv_SIG) MCon_imps_Some LSubPrefL2_def \<open>l = hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)\<close> 
          assms hash_suffixes_associative lessThanSome_imps_Locs2 lessThanTopLocs_def nat_less_le)
    then have "TypedMemSubPrefPtrs (memory st') x11' x12' l stl1" using idef lneq by blast
    then show False using lneq2 lsubloc
    proof(induction x12' arbitrary:x11' l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and>
         (l' = stl1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' stl1)" 
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' stl1)" by blast
      have "LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using MTArray.prems(3) 
        using LSubPrefL2_def hash_suffixes_associative by auto
      then have l'def:"l' = (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'))" using i'def assms by blast
      then have l'neq:"l' \<noteq> stl1" using MTArray.prems(2) i'def by blast
      then have "TypedMemSubPrefPtrs (memory st') x1 x12' l' stl1" using i'def by simp
      moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using l'def l'neq 
        by (smt (verit, ccfv_SIG) MCon_imps_Some LSubPrefL2_def \<open>LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))\<close> 
            assms hash_suffixes_associative lessThanSome_imps_Locs2 lessThanTopLocs_def less_not_refl)
      ultimately show ?case using MTArray.IH[of x1 l'] 
        by (simp add: \<open>LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))\<close> l'def)
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed
  then show ?thesis using MTArray by simp
next
  case (MTValue x2)
  then show ?thesis 
    by (smt (verit, ccfv_threshold) MCon_imps_Some LSubPrefL2_def TypedMemSubPrefPtrs.simps(1) assms(1) assms(2) assms(3) assms(4) hash_suffixes_associative lessThanSome_imps_Locs2 lessThanTopLocs_def nless_le)
qed

lemma TS_imps_InDenLessStack3:
  assumes "MCon (MTArray x11' x12') (memory st) stl1"
    and "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
    and "(\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None)"
    and "(\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<longrightarrow> accessStore locs (memory st') = accessStore locs (memory st)"
    and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<and> accessStore l (memory st') = Some (MPointer l') \<longrightarrow> l' = l"
    and "MCon tp2 (memory st') stl2"
  shows "\<not> TypedMemSubPrefPtrs (memory st') x11' x12' stl1 stl2" 
proof(cases x12')
  case (MTArray x11 x12)
  have "\<not> TypedMemSubPrefPtrs (memory st') x11' (MTArray x11 x12) stl1 stl2" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:"\<exists>i<x11'. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs (memory st') x11 x12 l stl2)"
    then obtain i l where idef:"i<x11' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs (memory st') x11 x12 l stl2)" by blast
    have "\<not> LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using assms(1,2,3,4,5,6) LSubPrefL2_def 
      by (metis MConArrayPointers MTArray gr_zeroI idef le_refl less_nat_zero_code option.discI)
    then have mconl:"MCon (MTArray x11 x12) (memory st) l" using assms(1,5) MTArray idef 
      by (metis MCon_imps_sub_Mcon)
    then have lneq:"l \<noteq> stl2" 
      by (metis MCon_imps_Some assms(2) assms(3) assms(4) le_refl lessThanSome_imps_Locs2 lessThanTopLocs_def less_not_refl option.discI)
    then have lsubloc:"\<not> LSubPrefL2  l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using assms LSubPrefL2_def hash_suffixes_associative mconl idef 
      by (metis (no_types, lifting) MCon_imps_Some le_refl option.discI)
    have lneq2:"\<forall>i<x11. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl2" 

      using MemLSubPrefL2_specific_imps_general assms(2) lsubloc by blast
    then have "TypedMemSubPrefPtrs (memory st') x11 x12 l stl2" using idef lneq by blast
    then show False using lneq2 lsubloc mconl
    proof(induction x12 arbitrary:x11 l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = stl2 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' stl2)" 
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = stl2 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' stl2)" by blast
      then have mconl':"MCon (MTArray x1 x12')  (memory st) l'" using assms(5) MTArray(5) 
        by (metis MCon_imps_sub_Mcon MTArray.prems(3) MemLSubPrefL2_specific_imps_general)
      then have l'neq:"l' \<noteq> stl2" using i'def MTArray.prems(2,4)  assms(2,3,4,5) 
        by (metis MCon_imps_Some antisym_conv2 le_refl lessThanSome_imps_Locs2 lessThanTopLocs_def option.distinct(1))
      then have "TypedMemSubPrefPtrs (memory st') x1 x12' l' stl2" using i'def by simp
      then have l'subloc:"\<not> LSubPrefL2  l'  (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using l'neq assms i'def mconl' 
        by (metis MCon_imps_Some le_refl lessThanSome_imps_Locs2 lessThanTopLocs_def less_not_refl option.discI)
      moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl2" using l'subloc assms(2) 
        by (meson MemLSubPrefL2_specific_imps_general)
      ultimately show ?case using MTArray.IH[of x1 l'] i'def 
        using l'neq mconl' by blast
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed
  then show ?thesis using MTArray by simp
next
  case (MTValue x2)
  then show ?thesis using assms(1) assms(2) assms(3) by fastforce
qed

(*2 part proof. All subptrs of stl1 cannot be melsubpref of toploc and all subptrs of stl2 point to self and so need to bu memlsuvpref*)
lemma subPtrs_nonTop:
  assumes "MCon (MTArray x11' x12') (memory st) stl1"
    and "(\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None)"
    and "(\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st))) \<longrightarrow> accessStore locs (memory st') = accessStore locs (memory st)"
    and "TypedMemSubPrefPtrs (memory st') x11' x12' stl1 dloc1"
  shows "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" 
proof(cases x12')
  case (MTArray x11 x12)
  then obtain i l where idef:"i<x11' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (memory st') = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x11 x12 l dloc1)" 
    using assms by auto
  have "\<not> LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st)))" using assms(1,2) LSubPrefL2_def 
    by (metis MConArrayPointers MTArray gr_zeroI idef le_refl less_nat_zero_code option.discI)
  then have mconl:"MCon (MTArray x11 x12) (memory st) l" using assms(1,4) MTArray idef 
    by (metis MCon_imps_sub_Mcon)
  then have lsubloc:"\<not> LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using assms(2) LSubPrefL2_def hash_suffixes_associative mconl idef 
    by (metis (no_types, lifting) MCon_imps_Some le_refl option.discI)
  show ?thesis 
  proof
    assume *:"LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
    show False
    proof(cases "l = dloc1")
      case True
      then show ?thesis
        using "*" assms(2,3) lessThanSome_imps_Locs2[of st dloc1 "0" "MValue _" "toploc (memory st)"] lessThanSome_imps_Locs2[of st dloc1 "0" "MPointer _" "toploc (memory st)"]
          lessThanTopLocs_def[of "memory st"] mcon_accessStore[of x11 x12 "memory st" dloc1 "0"] mconl by fastforce
    next
      case False
      then have lneq2:"\<forall>i<x11. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using mconl lsubloc idef assms(3,4)  
        using "*" MemLSubPrefL2_specific_imps_general by blast
      then have "TypedMemSubPrefPtrs (memory st') x11 x12 l dloc1" using idef False by blast
      then show ?thesis using lneq2 lsubloc mconl
      proof(induction x12 arbitrary:x11 l)
        case (MTArray x1 x12')
        have "\<exists>i'<x11. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1)" 
          using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
        then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st') = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1)" by blast
        then have mconl':"MCon (MTArray x1 x12')  (memory st) l'" using assms(4) MTArray(5) 
          by (metis MCon_imps_sub_Mcon MTArray.prems(3) MemLSubPrefL2_specific_imps_general)
        then have l'neq:"l' \<noteq> dloc1" using i'def MTArray.prems(2,4)  assms(2,3)
          using "*" MCon_imps_Some lessThanSome_imps_Locs lessThanSome_imps_Locs2 lessThanTopLocs_def by blast
        then have "TypedMemSubPrefPtrs (memory st') x1 x12' l' dloc1" using i'def by simp
        then have l'subloc:"\<not> LSubPrefL2  l'  (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))" using l'neq assms i'def mconl' 
          by (metis MCon_imps_Some le_refl lessThanSome_imps_Locs2 lessThanTopLocs_def less_not_refl option.discI)
        moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using l'subloc 
          using "*" MemLSubPrefL2_specific_imps_general by blast
        ultimately show ?case using MTArray.IH[of x1 l'] i'def 
          using l'neq mconl' by blast
      next
        case (MTValue x)
        then show ?case by auto
      qed 
    qed
  qed
next
  case (MTValue x2)
  then show ?thesis using assms(1,2,5) by fastforce
qed

lemma PreExistMconNotChangeByToploc:
  assumes "(\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "(\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (memory st) = None)"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t(toploc (memory st))) \<longrightarrow> accessStore locs (memory st) = accessStore locs m"
    and "MCon tp1 (memory st) stl1"
  shows "MCon tp1 m stl1" using assms(4)
proof(induction tp1 arbitrary: stl1)
  case (MTArray x1 struct)
  then have accessSome:"\<forall>i'<x1. \<exists>y. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st) = Some y" 
    by (metis bot_nat_0.not_eq_extremum less_nat_zero_code mcon_accessStore)
  moreover have accessSame:"\<forall>i'<x1. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (memory st) = accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m" using calculation
    by (metis Read_Show_nat'_id antisym_conv1 assms(2,3) option.distinct(1) readLintNotEqual)

  have "\<forall>i<x1.
(case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
  | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
  | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix i' assume asm3:"i'<x1"
    show "case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m of None \<Rightarrow> False 
        | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
        | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m")
      case None
      then show ?thesis using accessSome accessSame asm3 by auto
    next
      case (Some a)
      then show ?thesis 
      proof(cases a)
        case (MValue x1')
        then show ?thesis using accessSome accessSame Some asm3 MTArray by (cases struct; auto)
      next
        case (MPointer x2)
        then have "MCon struct (memory st) x2" using accessSome accessSame Some asm3 MTArray 
          by (metis MconSameTypeSameAccessWithTyping)
        then have "MCon struct m x2" using MTArray by simp
        then show ?thesis using accessSome accessSame Some asm3 MTArray MPointer by (cases struct; auto)
      qed
    qed
  qed
  moreover have "x1>0" using MTArray(2) unfolding MCon.simps by presburger
  moreover have "(\<exists>p. accessStore stl1 m = Some (MPointer p)) \<or> accessStore stl1 m = None" using calculation(3) MTArray unfolding MCon.simps 
    by (metis accessSome lessThanSome_imps_Locs2 lessThanTopLocs_def assms(1,2,3) nat_less_le )
  ultimately show ?case using MCon.simps(2)[of x1 struct m ] by simp
next
  case (MTValue x')
  then show ?case 
    by (metis (no_types, lifting) Read_Show_nat'_id case_optionE lessThanSome_imps_Locs lessThanTopLocs_def assms(1,2,3) readLintNotEqual MCon.simps(1))
qed

subsection \<open>Balances and Svalues conform\<close>
definition balanceTypes :: "Accounts \<Rightarrow> bool" where
  "balanceTypes acc = (\<forall>adv. typeCon (TUInt b256) (bal (acc adv)))"

definition addressFormat::"Address \<Rightarrow> bool"
  where "addressFormat cur = (typeCon TAddr cur)"

definition svalueTypes :: "Valuetype \<Rightarrow> bool" where
  "svalueTypes sval = typeCon (TUInt b256) sval"

subsection \<open>Compatiable pointers. \<close>



(*Type of the parent, location of the parent, type of the subprefix, location of the subprefix*)
primrec Subpref :: "STypes \<Rightarrow> Location \<Rightarrow> STypes \<Rightarrow> Location \<Rightarrow> bool"
  where
    "Subpref (STValue typ) Modulatedparent typ2 subloc = ((Modulatedparent = subloc) \<and> typ2 = (STValue typ))"
  |"Subpref (STArray len arr) Modulatedparent typ2 subloc = (((STArray len arr) = typ2 \<and> Modulatedparent = subloc) 
                                                        \<or> ( \<exists>i::nat \<in> {0::nat..len-1}. Subpref arr (hash Modulatedparent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) typ2 subloc))"
  |"Subpref (STMap fromTyp toTyp) Modulatedparent typ2 subloc = (((STMap fromTyp toTyp) = typ2 \<and> Modulatedparent = subloc) 
                                                            \<or>(\<exists>i::String.literal. (typeCon fromTyp i) \<and> Subpref toTyp (hash Modulatedparent i) typ2 subloc))"


lemma  "\<not>Subpref  (STArray 3 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''4.1.5'')" using Subpref.simps hash_def by simp? eval
lemma  "Subpref  (STArray 5 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''1.1.5'')" using Subpref.simps hash_def by simp? eval
lemma  "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STValue TBool)) (STR ''1.1.1.1.5'') " using Subpref.simps hash_def by simp? eval
lemma  "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STArray 3 (STValue TBool))) (STR ''1.1.1.5'') " using Subpref.simps hash_def by simp? eval

(*
Ensures that if two pointer contained in the den value point to locations which are prefixes of one
another their base types must be compatible.
Needed as when proving typeSafety of two stacklocs that contain storage pointers it is impossible to
conclude SCon of the current denvalue pair without a link between the denvalue pair we are looking at
and the denvalue location referenced by lexp (ref i t) 
*)
(*
Not sure about this definition.
Doesnt quite capture my case. 
So we have a ref which points to a y in denvalue. 
That y then gets accessed to return some stl2 (in lexp). However that then goes into ssel and may
change due to hashing, meaning the isSubPrefix stl1 stl2 isnt what we split on but it is in fact
isSubPrefix stl1 (Some arbitrary extension of stl2)
Could do a lemma that show that isSubPrefix is transitive over ssel. So if  
isSubPrefix stl1 (Some arbitrary extension of stl2) holds the original isSubPrefix stl2 must hold.

Further it is possible that lv passed to lexp returns a store loc directly from the denvalue
Then there is no accessStore to compare

*)




lemma tlb:
  assumes "Subpref tp1 stl1 tp2 stl2"
    and "stl1 \<noteq> stl2"
  shows "\<exists>i. hash stl1 i = stl2"
  using assms
proof(induction tp1 arbitrary:stl1)
  case (STArray x1 tp1)
  then have a10:"(\<exists>i\<in>{0..x1 - 1}. Subpref tp1 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp2 stl2)" 
    using Subpref.simps(2)[of x1 tp1 stl1 tp2 stl2] by auto
  then obtain i where idef:"(i\<in>{0..x1 - 1} \<and> Subpref tp1 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp2 stl2)" by auto
  then show ?case
  proof(cases "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = stl2")
    case True
    then show ?thesis using idef by auto
  next
    case False
    then show ?thesis using STArray(1)[of "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] idef a10 hash_suffixes_associative by auto
  qed
next
  case (STMap x1 tp1)
  then have a10:" (\<exists>i. typeCon x1 i \<and> Subpref tp1 (hash stl1 i) tp2 stl2)" 
    using Subpref.simps(3)[of x1 tp1 stl1 tp2 stl2] by auto
  then obtain i where idef:"typeCon x1 i \<and> Subpref tp1 (hash stl1 i) tp2 stl2" by auto
  then show ?case 
  proof(cases "(hash stl1 i) = stl2")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis using STMap(1)[of "(hash stl1 i)"] idef a10 hash_suffixes_associative by auto
  qed
next
  case (STValue x)
  then show ?case using Subpref.simps(1) by simp
qed

definition typeCompat::"(String.literal, Type \<times> Denvalue) fmap   \<Rightarrow> Stack \<Rightarrow> MemoryT \<Rightarrow> StorageT \<Rightarrow> CalldataT \<Rightarrow> bool"
  where "typeCompat den sckO mem sto cd = (\<forall>t l. (t, l) |\<in>| fmran (den)
            \<longrightarrow> (case l of (Stackloc loc) \<Rightarrow>
                  (case (accessStore loc sckO) of
                   Some(KValue val) \<Rightarrow> 
                      (case t of (Value typ) \<Rightarrow> typeCon typ val
                       | _ \<Rightarrow> False )
                   | Some(KMemptr stloc) \<Rightarrow>
                      (case t of (Memory struct) \<Rightarrow> MCon struct mem stloc 
                        | _ \<Rightarrow> False
                      )
                   | Some(KCDptr stloc) \<Rightarrow> 
                      (case t of (Calldata struct) \<Rightarrow> MCon struct cd stloc
                        | _ \<Rightarrow> False
                      )
                   | Some(KStoptr stloc) \<Rightarrow>
                        (case t of (Storage struct) \<Rightarrow> SCon struct stloc sto
                          | _ \<Rightarrow> False)
                      
                   | _ \<Rightarrow> False)
                | (Storeloc loc) \<Rightarrow> 
                      (case t of (Storage typ) \<Rightarrow> SCon typ loc sto
                        | _ \<Rightarrow> False)
                )
          )"

subsection \<open>Shorthand - Suplementary lemmas\<close>
text \<open>Collection of lemmas which shorten common proof obligations\<close>

text \<open>Support functions to simplify the typeCon expressions definition \<close>
fun extractValueType :: "Stackvalue \<Rightarrow> Valuetype" where
  "extractValueType (KValue v) = v"
| "extractValueType (KCDptr v) = v"
| "extractValueType (KMemptr v) = v"
| "extractValueType (KStoptr v) = v"





lemma MCon_imps_TypedStoSubPref_Some:
  assumes "TypedStoSubPref x' loc t'"
    and "cps2mTypeCompatible t' t"
    and "MCon t m loc"
    and "\<forall>l l'. TypedStoSubPref l loc t' \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
  shows "\<exists>v. accessStore x' m = Some v"
  using assms 
proof(induction t' arbitrary:loc t)
  case (STArray x1 t')
  obtain i where a1:"i<x1 \<and> (TypedStoSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' \<or> x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
    using STArray.prems(1) unfolding TypedStoSubPref.simps by blast
  obtain ml ma where a2:"t = MTArray ml ma \<and> x1>0 \<and> ml = x1 \<and> cps2mTypeCompatible t' ma" 
    using STArray.prems(2) cps2mTypeCompatible.simps 
    by (metis mtype_size.cases)
  then have mc:"MCon (MTArray x1 ma) m loc " using STArray.prems(3) by simp
  then have acc:"\<forall>i<x1. \<exists>v. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m  = Some v" 
    by (meson a2 mcon_accessStore)
  then show ?case 
  proof(cases "x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
    case True
    then show ?thesis using acc a1 by simp
  next
    case False
    then have a10:"TypedStoSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t'" using a1 by simp
    then show ?thesis 
    proof(cases ma)
      case (MTArray x11 x12)
      then obtain p where acc2:"accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer p)" 
        using mc MConArrayPointers a1 by blast
      then have "p = (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using STArray.prems 
        using a1 TypedStoSubPref.simps(2) by blast
      moreover have "MCon ma m (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) " using mc a1 acc2 calculation 
        using MCon_imps_sub_Mcon by blast
      ultimately show ?thesis using STArray.IH[OF a10 _ ] a2 
        using STArray.prems(4) a1 TypedStoSubPref.simps(2) by blast
    next
      case (MTValue x2)
      then have mc2:"MCon ma m (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using mc a1 
        using MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val by presburger
      moreover have "\<forall>l l'. TypedStoSubPref l (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' 
                    \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
        using STArray.prems a1 by auto
      ultimately show ?thesis using STArray.IH[OF a10 _ mc2] a2 by simp
    qed
  qed
next
  case (STMap x1 t')
  then show ?case by auto
next
  case (STValue x)
  then show ?case 
    by (metis MConAccessSame.simps(1) SameMCon_imps_MConAccessSame TypedStoSubPref.simps(1) cps2mTypeCompatible.simps(6) mtype_size.cases)
qed

lemma compatible_TypedStoSubPref_imps_TypedMemSubPref:
  assumes "cps2mTypeCompatible st mt"
  shows "TypedStoSubPref x' l st = TypedMemSubPref x' l mt"
proof
  assume "TypedStoSubPref x' l st"
  then show "TypedMemSubPref x' l mt" using assms
  proof(induction st arbitrary:mt l)
    case (STArray x1 st)
    then show ?case 
      by (smt (verit) STypes.inject(1) TypedMemSubPref.simps(2) TypedStoSubPref.simps(2)
          cps2mTypeCompatible.elims(2) cps2mTypeCompatible.simps(3))
  next
    case (STMap x1 st)
    then show ?case 
      by simp
  next
    case (STValue x)
    then show ?case 
      by (metis TypedMemSubPref.simps(1) TypedStoSubPref.simps(1) cps2mTypeCompatible.simps(6) extractType.cases)
  qed
next 
  assume "TypedMemSubPref x' l mt"
  then show "TypedStoSubPref x' l st " using assms
  proof(induction mt arbitrary: st l)
    case (MTArray x1 mt)
    then show ?case 
      by (smt (verit, ccfv_threshold) MTypes.inject(1) cps2mTypeCompatible.elims(1) cps2mTypeCompatible.simps(6) TypedMemSubPref.simps(2)
          TypedStoSubPref.simps(2))
  next
    case (MTValue x)
    then show ?case 
      by (metis STypes.exhaust TypedMemSubPref.simps(1) TypedStoSubPref.simps(1) cps2mTypeCompatible.simps(3,4))
  qed
qed





context statement_with_gas
begin

text \<open>Checks that a given environment and state are considered fully initialised this meaning that the contract has an initialised account
                and all the contract variables have been initialised in the denvalue. 
                These two processes are the first things that would need to be done when creating a new environment (check statement NEW)\<close>
definition fullyInitialised::"Environment \<Rightarrow> Accounts \<Rightarrow> Stack \<Rightarrow> bool"
  where "fullyInitialised env acc sk = ((\<exists>c. type (acc (address env)) = Some (Contract c) \<and> contract env = c) \<and>
        (\<forall>id ct dud v. ep $$ contract env = Some (ct, dud) \<and> ct $$ id = Some (Var v) \<longleftrightarrow> (denvalue env $$ id = Some (Storage v, Storeloc id)))
        \<and> (\<forall>t l p. (Storage t, Stackloc l) |\<in>| fmran (denvalue env) \<and> accessStore l sk = Some (KStoptr p) 
                    \<longrightarrow> (\<exists>t' l'. (Storage t', Storeloc l') |\<in>| fmran (denvalue env) \<and> CompStoType t' t l' p))
)"

definition AddressTypes::"Accounts \<Rightarrow> bool"
  where "AddressTypes ac =  (\<forall>c adv ct dud. type (ac adv) = Some (Contract c) \<longrightarrow> ep $$ (c) = Some (ct,dud) \<and> addressFormat adv)"

(*A specifc rule here would be that identifier for variables cannot contain a dot, 
  This would achieve the same result be would not require the TypedStoSubpref definition 
  and could be a global assumption of ep. 
*)
definition methodVarsNoPref :: "bool" where
  "methodVarsNoPref = (\<forall>c ct dud i1 i2 t1 t2. i1 \<noteq> i2 \<and> ep $$ c = Some(ct,dud) \<and> ct $$ i1 = Some (Var t1) \<and> ct $$ i2 = Some (Var t2) 
                                  \<longrightarrow> (\<not>TypedStoSubpref i1 i2 t2) \<and> (\<not>TypedStoSubpref i2 i1 t1))"

definition safeContract :: "(Address \<Rightarrow> StorageT)  \<Rightarrow> bool" where 
  "safeContract sto = (\<forall>e ct dud i tp. ep $$ contract (e::Environment) = Some (ct, dud) 
                                \<and> fmlookup ct i = Some (Var tp) \<longrightarrow> 
                                (SCon tp i (sto (address (e::Environment)))))"



subsection \<open>Typesafe environments\<close>
text \<open>The TypeSafe defition ensures that a given env, stack, memory, accounts, storage and calldata
      are Typesafe.
In this instance typesafety is defined over two sets of properties. An instance of enironment must satisfy
certain operation characteristics. 
And 2 all types and locations defined in the denvalue of the env must ensure that the String representation
of the value must conform to the respective type.\<close>
definition TypeSafe :: "Environment \<Rightarrow> Accounts \<Rightarrow> Stack \<Rightarrow> MemoryT \<Rightarrow> (Address \<Rightarrow> StorageT) \<Rightarrow> CalldataT \<Rightarrow> bool"
  where "TypeSafe ev acc sck mem sto cd= (
          typeCompat (denvalue ev) sck mem (sto (address ev)) cd \<and>
          (unique_locations (denvalue ev)) \<and>
          (compPointers sck (denvalue ev)) \<and>
          (compMemPtrs sck mem (denvalue ev)) \<and>
          (lessThanTopLocs sck) \<and> (lessThanTopLocs mem) \<and> (lessThanTopLocs cd) \<and>
          (addressFormat (address ev)) \<and>
          (addressFormat (sender ev)) \<and>
          AddressTypes(acc)\<and>
          (safeContract sto) \<and>
          (methodVarsNoPref) \<and>
          (balanceTypes acc) \<and>
          (svalueTypes (svalue ev)))"


subsection \<open>All stack locations in the devalue must have a valid value in the stack\<close>
lemma typeSafeAllStacklocsExist: 
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(t, l2) |\<in>| fmran (denvalue ev)"
    and "l2 = Stackloc l"
  shows "\<exists>v. accessStore l sck = Some v"
proof -
  have "\<forall>t l. (t, l) |\<in>| fmran (denvalue ev) \<longrightarrow> 
        (case l of (Stackloc loc) \<Rightarrow> 
          (case (accessStore loc sck) of
            Some(KValue val) \<Rightarrow> (case t of (Value typ) \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
          | Some(KMemptr stloc) \<Rightarrow> (case t of (Memory struct) \<Rightarrow> MCon struct mem stloc | _ \<Rightarrow> False)
          | Some(KCDptr stloc) \<Rightarrow> (case t of (Calldata struct) \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | Some(KStoptr stloc) \<Rightarrow> (case t of (Storage struct) \<Rightarrow> SCon struct stloc (sto (address ev)) | _ \<Rightarrow> False)
          | _ \<Rightarrow> False)
        | (Storeloc loc) \<Rightarrow> (case t of (Storage typ) \<Rightarrow> SCon typ loc (sto (address ev)) | _ \<Rightarrow> False))"
    using assms(1) unfolding TypeSafe_def typeCompat_def by simp
  then have "case l2 of (Stackloc loc) \<Rightarrow> \<exists>v. accessStore loc sck = Some v"
    using assms(2) assms(3)  Denvalue.simps(5) case_optionE by fastforce
  then show ?thesis using assms(3) by simp
qed



subsection \<open>astack does not impact unique locations\<close>
lemma updateEnvUniqueLocs:
  assumes "TypeSafe ev' (accounts st) sck' mem' (storage st) cd'"
    and "(k',e) = astack ip (v) (p) (sck', ev')"
  shows "unique_locations (denvalue e)" unfolding unique_locations_def
proof(intros)
  have a10:"e = (updateEnv ip (v) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck'))) ev')" using assms(2) by simp
  then have a15:"denvalue e = denvalue(ev' \<lparr> denvalue := fmupd ip ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck')))) (denvalue ev') \<rparr>)" by simp
  then have a17:"(denvalue e) $$ ip = Some  ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck'))))" by simp
  have a20:"unique_locations (denvalue ev')" using  assms(1) TypeSafe_def by simp
  have a30:"lessThanTopLocs sck'" using assms(1) TypeSafe_def by simp
  fix x' y
  assume aULoc:"x' |\<in>| fmran (denvalue e) \<and> y |\<in>| fmran (denvalue e) \<and> snd x' = snd y"
  then have a40:" (\<forall>tloc loc. toploc sck' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc sck' = None)" using lessThanTopLocs_def Read_Show_nat'_id a30 by auto
  then have "\<forall>x y. \<not>((denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck'))))" using TypeSafe_def assms typeSafeAllStacklocsExist fmranI a40  
    by (metis LSubPrefL2_def nle_le option.distinct(1) prod.exhaust_sel)
  then have a50:"\<forall>x' y. ((denvalue e) $$ x'  = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck')))) \<longrightarrow> x' = ip \<and> (fst y) = (v)" using a30 a15 fmranI  by auto
  show "x' = y"
  proof(cases "snd x' = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck')))")
    case True
    then obtain x'' where "(denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have "x'' = ip" using a50 True by blast
    then show ?thesis using a50 aULoc True by (metis fmlookup_ran_iff prod_eq_iff) 
  next
    case False  
    then obtain x'' where a140:"(denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have a150:"x'' \<noteq> ip" using a50 False a17 by (metis option.inject snd_conv)
    have a160:"\<forall>x y. x \<noteq> ip \<and> (denvalue e) $$ x = Some y \<longrightarrow> (denvalue ev') $$ x = Some y" using a15 by simp
    then have "(denvalue ev') $$ x'' = Some x'" using a140 a150 by blast (*TODO: REVISIT AS THIS COULD BE SIMPLIFIED MOST LIKELY*)
    then show ?thesis  using aULoc a20 unique_locations_def False a160 a17 by (metis fmranE fmranI option.inject snd_conv) 
  qed
qed

lemma sameSckTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Value typ), (Stackloc loc)) |\<in>| fmran (denvalue ev) \<and> accessStore loc sck = Some (KValue val) \<longrightarrow> typeCon typ val" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce 

lemma sameMemTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Memory struct), (Stackloc loc)) |\<in>| fmran (denvalue ev) \<and> accessStore loc sck = Some (KMemptr stloc) \<longrightarrow> MCon struct mem stloc" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameCdTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Calldata struct), (Stackloc loc)) |\<in>| fmran (denvalue ev) \<and> accessStore loc sck = Some (KCDptr stloc) \<longrightarrow> MCon struct cd stloc" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameStoTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Storage struct), (Stackloc loc)) |\<in>| fmran (denvalue ev) \<and> accessStore loc sck = Some (KStoptr stloc) \<longrightarrow>  SCon struct stloc (sto (address ev))" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameStoLocTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Storage struct), (Storeloc loc)) |\<in>| fmran (denvalue ev) \<longrightarrow>  SCon struct loc (sto (address ev))" using assms 
  unfolding TypeSafe_def typeCompat_def by fastforce

lemma typeSafeUnique:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "unique_locations (denvalue ev)" using assms unfolding TypeSafe_def by simp 

lemma typeSafeAccounts:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "balanceTypes acc" using assms unfolding TypeSafe_def by simp 

lemma typeSafeSvalue:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "svalueTypes (svalue ev)" using assms unfolding TypeSafe_def by simp 

lemma typeSafeCompPointers:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "compPointers sck (denvalue ev)" using assms unfolding TypeSafe_def by simp 

lemma lvID:
  assumes "lexp lv env cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l2, t'), g')"
  shows "\<exists>i. lv = Id i"
proof (cases lv)
  case (Id i)
  then show ?thesis by auto
next
  case (Ref i r)
  then have "lexp (Ref i r) env cd (st\<lparr>gas := g\<rparr>) g =
    (case denvalue env $$ i of None \<Rightarrow> throw Err
     | Some (tp, Stackloc l) \<Rightarrow>
         (case accessStore l (stack (st\<lparr>gas := g\<rparr>)) of None \<Rightarrow> throw Err
         | Some (KMemptr l') \<Rightarrow> (case tp of Memory x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.msel True t l' r env cd (st\<lparr>gas := g\<rparr>) \<bind> (\<lambda>(l'', t'). return (LMemloc l'', Memory t')))
         | Some (KStoptr l') \<Rightarrow> (case tp of Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.ssel t l' r env cd (st\<lparr>gas := g\<rparr>) \<bind> (\<lambda>(l'', t'). return (LStoreloc l'', Storage t'))) 
         | Some _ \<Rightarrow> throw Err)
     | Some (tp, Storeloc l) \<Rightarrow> (case tp of Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.ssel t l r env cd (st\<lparr>gas := g\<rparr>) \<bind> (\<lambda>(l', t'). return (LStoreloc l', Storage t'))))
     g" using lexp.simps(2)[of i r env cd "(st\<lparr>gas := g\<rparr>)" g] Ref by simp
  then have "\<not>(\<exists>l tp. lexp (Ref i r) env cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l, tp), g'))"
    by (auto split: option.splits prod.splits Denvalue.split_asm Type.splits Stackvalue.splits result.splits)
  then have False using assms Ref by simp
  then show ?thesis by simp
qed

lemma lexpDenStor:
  assumes "lexp lv env cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStoreloc l2, t'), g')"
    and "lv = Id x1"
  shows "(t', Storeloc l2) |\<in>| fmran (denvalue env)" using assms
proof -
  have "(denvalue env) $$ x1 = Some (t', Storeloc l2)" 
    using assms lexp.simps(1) by (simp split: option.split_asm prod.split_asm Denvalue.split_asm)
  then show ?thesis using Finite_Map.fmranI[of "(denvalue env)" x1 "(t', Storeloc l2)"] by simp
qed

lemma lexpDen:
  assumes "lexp lv env cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l2, t'), g')"
    and "lv = Id i"
  shows "(t', Stackloc l2) |\<in>| fmran (denvalue env)"
proof - 
  have "(case (denvalue env) $$ i of
      Some (tp, (Stackloc l)) \<Rightarrow> return (LStackloc l, tp)
    | Some (tp, (Storeloc l)) \<Rightarrow> return (LStoreloc l, tp)
    | _ \<Rightarrow> throw Err) g = Normal ((LStackloc l2, t'), g')" using lexp.simps(1) assms by auto
  then have "(denvalue env) $$ i = Some (t', Stackloc l2)" by (simp split: option.split_asm prod.split_asm Denvalue.split_asm)
  then show ?thesis using Finite_Map.fmranI[of "(denvalue env)" i "(t', Stackloc l2)"] by simp
qed

lemma lexpStackloc_imps_inDen:
  assumes "lexp lv env cd (st\<lparr>gas := g\<rparr>) g = Normal ((LStackloc l2, t'), g')"
  shows "(t', Stackloc l2) |\<in>| fmran (denvalue env)" using assms lexpDen lvID by metis

lemma stackLocs_imp_NotDen:
  assumes "lessThanTopLocs sck'"
    and "TypeSafe ev' (accounts st) sck' mem' (storage st) cd'"
  shows "\<forall>x y. (denvalue ev') $$ x = Some y \<longrightarrow> snd y \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck')))" 
proof - 
  have " accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc sck')) sck' = None" using lessThanTopLocs_def Read_Show_nat'_id assms(1) using LSubPrefL2_def by auto
  then show ?thesis using assms(2) unfolding TypeSafe_def typeCompat_def using fmranI by fastforce
qed

lemma TS_imps_InDenLessStack:
  assumes "TypeSafe env acc sck mem sto cd"
    and "((Memory (MTArray x11 x12)), (Stackloc loc)) |\<in>| fmran (denvalue env)"
    and "(accessStore loc sck') = Some (KMemptr stl2)"
    and "tloc = (toploc mem) \<and> LSubPrefL2 stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
    and "MCon (MTArray x11 x12) mem stl2"
  shows "\<not>TypedMemSubPrefPtrs mem x11 x12 stl2 stl1" 
proof(cases x12)
  case (MTArray x11' x12')
  then have  Mcon:"MCon (MTArray x11 x12) mem stl2" using assms(1) unfolding TypeSafe_def using assms(2,3,4,5) 
    by fastforce
  have t:"((\<forall>tloc loc. toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def by auto

  have "\<not> TypedMemSubPrefPtrs mem x11 (MTArray x11' x12') stl2 stl1" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:"\<exists>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x11' x12' l stl1)"
    then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x11' x12' l stl1)" by blast
    then have neq:"l \<noteq> stl1" using Mcon 
      by (metis MCon_imps_Some MCon_imps_sub_Mcon LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific not_Some_eq t)
    then have neqSub:"\<forall>i<x11'. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using t assms(4) idef Mcon 
      by (metis (mono_tags, opaque_lifting) MCon_imps_Some MCon_imps_sub_Mcon LSubPrefL2_def MemLSubPrefL2_specific_imps_general Not_Sub_More_Specific le_refl not_None_eq)
    have mconl: "MCon (MTArray x11' x12') mem l" using idef Mcon 
      using MCon_imps_sub_Mcon MTArray by blast
    then have "TypedMemSubPrefPtrs mem x11' x12' l stl1" using idef neq by simp
    then show False using neqSub mconl
    proof(induction x12' arbitrary: x11' l)
      case (MTArray x1 x12')
      then have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs mem x1 x12' l' stl1)"  
        unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs mem x1 x12' l' stl1)" by blast
      then have l'neq:"l' \<noteq> stl1" using MTArray.prems 
        by (metis MCon_imps_Some LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific mcon_typedptrs_ims_existance not_Some_eq t)
      then have "TypedMemSubPrefPtrs mem x1 x12' l' stl1" using i'def by simp
      have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using i'def l'neq MTArray.prems 
        by (metis MCon_imps_Some LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific mcon_typedptrs_ims_existance not_Some_eq t)
      then show ?case using MTArray.IH[of x1 l'] l'neq MTArray.prems(3) i'def by fastforce
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed

  then show ?thesis using MTArray by auto

next
  case (MTValue x2)
  have Mcon:"MCon (MTArray x11 x12) mem stl2" using assms(1) unfolding TypeSafe_def using assms(2,3,4,5) 
    by fastforce
  have t:"((\<forall>tloc loc. toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def by auto
  have " \<not>TypedMemSubPrefPtrs mem x11 (MTValue x2) stl2 stl1" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:" \<exists>i<x11. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1"
    then show False using Mcon assms t 
      by (metis MCon_imps_Some LSubPrefL2_def MemLSubPrefL2_specific_imps_general Not_Sub_More_Specific le_refl not_Some_eq)
  qed
  then show ?thesis using MTValue by simp
qed


lemma typeSafe_noDenElementOverToploc_mem:
  assumes " TypeSafe env (accounts st) (stack st) (memory st) (storage st) cd"
    and "((Memory struct), (Stackloc loc)) |\<in>| fmran (denvalue env)"
    and "(accessStore loc (stack st)) =  Some(KMemptr stloc)"
  shows "\<not>LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
proof
  assume *:"LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc (memory st)))"
  have h1:"((\<forall>tloc loc. toploc (memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<longrightarrow> accessStore loc (memory st) = None) \<and>
   (\<forall>loc y. accessStore loc (memory st) = Some y \<longrightarrow> (\<exists>tloc<toploc (memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))" 
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def  by blast
  have h2:"MCon struct (memory st) stloc" using assms unfolding TypeSafe_def typeCompat_def by fastforce
  then show False using * h1 
    using MCon_imps_Some lessThanSome_imps_Locs lessThanSome_imps_Locs2 lessThanTopLocs_def by blast
qed



lemma typeSafeAllPtrsNotTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(Memory t, Stackloc l) |\<in>| fmran (denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "ptr \<noteq> ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem) \<and> 
        (\<forall>len2 arr2. \<not>TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) ptr)\<and>
        (\<forall>len2 arr2. t = (MTArray len2 arr2) \<longrightarrow> \<not>TypedMemSubPrefPtrs mem len2 arr2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))) \<and>
        (\<forall>len2 arr2 len1 arr1 locs. t = (MTArray len2 arr2) \<longrightarrow> (\<nexists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc
                                                                        \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) dloc))"
proof intros
  have ptrMCon:"MCon t mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show notTop:"ptr \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))" using ptrMCon toplocs unfolding lessThanTopLocs_def 
    by (metis MCon_imps_Some LSubPrefL2_def dual_order.refl option.distinct(1))
  fix len2 arr2
  show notSub:"\<not> TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) ptr" 
  proof
    assume *:"TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) ptr"
    show False
    proof(cases arr2)
      case (MTArray x11 x12)
      then have "(\<exists>i<len2. \<exists>l. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
          \<and> (l = ptr \<or> TypedMemSubPrefPtrs mem x11 x12 l ptr))" 
        using * TypedMemSubPrefPtrs.simps(2)[of mem len2 x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))" ptr]
        by blast
      then show ?thesis using SomeA noneA by auto
    next
      case (MTValue x2)
      then show ?thesis using SomeA noneA * 
            TypedMemSubPrefPtrs.simps(1)[of mem len2 x2 "(ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))" ptr] 
        using hash_suffixes_associative by force
    qed
  qed
  assume tDef:"t = MTArray len2 arr2"
  show "\<not> TypedMemSubPrefPtrs mem len2 arr2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))"
    using SomeA noneA 
    by (metis MCon_imps_Some mcon_typedptrs_ims_existance option.distinct(1) ptrMCon tDef)

  fix len1 arr1 locs
  show "\<nexists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
        \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) dloc "
  proof
    assume **:"\<exists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
                \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) dloc"
    then obtain dloc where dlocDef:"TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
                \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) dloc" by blast
    then consider (ArrArr) l1 a1 l2 a2 where "arr1 = MTArray l1 a1 \<and> arr2 = MTArray l2 a2 "
      | (ArrVal) l1 a1 v where "arr1 = MTArray l1 a1 \<and> arr2 = MTValue v"
      | (ValArr) l2 a2 v where "arr2 = MTArray l2 a2 \<and> arr1 = MTValue v"
      | (ValVal) v1 v2 where "arr1 = MTValue v1 \<and> arr2 = MTValue v2" 
      apply (cases arr1) apply(cases arr2) apply blast apply blast 
      by (meson MTypes.exhaust)
    then show "False"
    proof(cases)
      case ArrArr
      then show ?thesis using dlocDef 
        by (simp add: noneA)
    next
      case ArrVal
      then show ?thesis using dlocDef 
        by (simp add: noneA)
    next
      case ValArr
      then show ?thesis using dlocDef 
        by (metis MCon_imps_Some hash_suffixes_associative mcon_typedptrs_ims_existance noneA option.distinct(1) ptrMCon
            TypedMemSubPrefPtrs.simps(1) tDef)
    next
      case ValVal
      then have "(\<exists>i<len2. hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc) \<and> (\<exists>i<len1. hash (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc)" 
        using dlocDef TypedMemSubPrefPtrs.simps(1) by simp
      then show ?thesis using ShowLNatDot hash_injective notTop by blast
    qed
  qed

qed


lemma typeSafeAllPtrsNotTop2:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(Memory t, Stackloc l) |\<in>| fmran (denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "
        (\<not>LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) ptr)"
proof intros
  have ptrMCon:"MCon t mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))" 
    using LSubPrefL2_def SomeA hash_suffixes_associative noneA by fastforce
  show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) ptr" 
    by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general \<open>\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))\<close>)

qed

lemma typeSafeAllMemPtrsCantTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(Memory tp, Stackloc l) |\<in>| fmran (denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "\<forall>len arr loc. tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc \<longrightarrow> 
        (\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) loc)"
proof intros
  fix len arr loc
  assume *:"tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc"
  then have ptrMCon:"MCon (MTArray len arr) mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by fastforce
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))" using * noneA SomeA 
    using TS_imps_InDenLessStack assms(1,2,3) ptrMCon by blast
  show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem)) loc" using * noneA SomeA 
    by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general \<open>\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (toploc mem))\<close>)
qed

end

end
theory BasicLemmas
  imports Main "$ISABELLE_HOME/src/HOL/Library/FSet" "$ISABELLE_HOME/src/HOL/Orderings" CombinatoricsBackground
begin

    
lemma psiRoot :
  shows "root (psi f) = root f"
proof -
  obtain children where n6767i6 : "f = (NODE (root f) children)"  by (metis (full_types) root.elims) 
  have "root (NODE (root f) (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children)))
                                  )
                              )
                              (fimage root children)
                     )) = (root f)" using root.simps root.elims  by metis
  then show "root (psi f) = root f" using root.simps root.elims n6767i6 psiDef  by (metis (no_types, lifting))
qed
  
  
  
lemma rootsPsi:
  "root |`| (\<Psi>\<^sub>\<phi>  otherForest1) = root |`| (otherForest1)"
proof -
  have "\<And>symbol2 . (root ( psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1))))) = symbol2" using root.simps  psiRoot by metis
  then have "root |`| (((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1))))) |`| (root |`| otherForest1)) = root |`| otherForest1" by auto
  then have "(root \<circ> ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) \<circ> root)) |`| otherForest1 = root |`| otherForest1" by auto
  then show ?thesis using psiF_def by auto
qed
  
  
  
lemma     factorPsiLemma   : "\<And>children . (\<alpha> \<diamondop> (finsert ((psi (NODE \<alpha> children))) fempty)) = \<Psi>\<^sub>\<phi> children"
proof -
  fix children
  show "(\<alpha> \<diamondop> (finsert ((psi (NODE \<alpha> children))) fempty)) = \<Psi>\<^sub>\<phi> children"
  proof -
    have "\<And>x . ((x \<in> (fset (\<alpha> \<diamondop> (finsert ((psi (NODE \<alpha> children))) fempty)))) = (x \<in> (fset (\<Psi>\<^sub>\<phi> children))))"
    proof (simp add : factorByRootSymbolF_lemma)
      show "\<And>x. (x \<in> \<alpha> \<diamondop>\<tau>\<lambda> {psi (NODE \<alpha> children)}) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))"
      proof (simp add : factorByRootSymbol_def)
        show "\<And>x. (root (psi (NODE \<alpha> children)) = \<alpha> \<and> x |\<in>| childrenSet (psi (NODE \<alpha> children))) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))"
        proof -
          fix x
            have "root (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children)))
                                  )
                              )
                              (fimage root children)
                     )) = \<alpha>" using root.simps root.elims  by auto
          then have "(root (psi (NODE \<alpha> children)) = \<alpha>)" using psiDef
            by metis 
              
              have "(fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children)))
                                  )
                              )
                              (fimage root children)
                     ) = ((\<Psi>\<^sub>\<phi> children))" 
              by (simp add : psiF_def)
                
              
              hence "x |\<in>| (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children)))
                                  )
                              )
                              (fimage root children)
                     ) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))"
                using notin_fset by force 
            then  have "x |\<in>| childrenSet (NODE \<alpha> (fimage (\<lambda> symbol2 .
                              psi (NODE symbol2 (\<Union>| (fimage childrenSet (childrenWithSymbol symbol2 children)))
                                  )
                              )
                              (fimage root children)
                     )) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))" by (metis childrenSet.simps notin_fset psiF_def) 
          hence "x |\<in>| childrenSet (psi (NODE \<alpha> children)) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))" using psiDef
            by (metis childrenSet.simps notin_fset psiF_def) 
        show "(root (psi (NODE \<alpha> children)) = \<alpha> \<and> x |\<in>| childrenSet (psi (NODE \<alpha> children))) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))"
          by (simp add: \<open>(x |\<in>| childrenSet (psi (NODE \<alpha> children))) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))\<close> \<open>root (psi (NODE \<alpha> children)) = \<alpha>\<close>) 
      qed
    qed
  qed
    then show "\<alpha> \<diamondop> {|psi (NODE \<alpha> children)|} = \<Psi>\<^sub>\<phi> children"
    proof -
      have "{t. t \<in> \<alpha> \<diamondop>\<tau>\<lambda> fset {|psi (NODE \<alpha> children)|}} = {t. t \<in> fset (\<Psi>\<^sub>\<phi> children)}"
        using \<open>\<And>x. (x \<in> fset (\<alpha> \<diamondop> {|psi (NODE \<alpha> children)|})) = (x \<in> fset (\<Psi>\<^sub>\<phi> children))\<close> factorByRootSymbolF_lemma(2) by force
      then have "fset (\<alpha> \<diamondop> {|psi (NODE \<alpha> children)|}) = fset (\<Psi>\<^sub>\<phi> children)"
        using factorByRootSymbolF_lemma(2) by auto
      then show ?thesis
        by (meson fset_inject)
    qed
  qed
qed
  
    
    
  
lemma psiPreservesPaths0:
  "\<And> (forest :: abc tree fset) . (heightForestBounded (\<Psi>\<^sub>\<phi> forest) n \<Longrightarrow> \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> forest) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (forest))"
proof (induct n)
  case 0
  from "0.prems"(1) have "\<Psi>\<^sub>\<phi> forest  = fempty" using heightForestBounded_def height.simps tree.exhaust
  proof -
    have "\<forall>t. \<exists>a f. NODE (a::abc) f = t"
      by (metis tree.exhaust)
    then show ?thesis
      by (metis "0.prems"(1) Suc_eq_plus1_left bot.extremum_uniqueI bot_nat_def equalsffemptyI height.simps heightForestBounded_def old.nat.distinct(2))
  qed 
  hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> forest) = fempty" using pathsInForest_def by (simp add: pathsInForest_def ffUnion_empty) 
  hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> forest) = fempty"   by (simp add: "0.prems"(1)) 
  hence "\<Psi>\<^sub>\<phi> forest = fempty" using pathForestEmpty by auto
  hence "forest = fempty" using psiF_def by auto
  then show ?case
    using \<open>\<Psi>\<^sub>\<phi> forest = {||}\<close> by auto
next
  case (Suc n)
  show ?case
  proof (simp add : pathsInForest_def)
    show "\<Union>| (\<delta>\<^sub>\<tau> |`| \<Psi>\<^sub>\<phi> forest) = \<Union>| (\<delta>\<^sub>\<tau> |`| forest)"
    proof (simp add : psiF_def)
      def children == "\<lambda> symbol2. (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest))"
      def rootSymbols == "root |`| forest"
      from children_def psiF_def rootSymbols_def  have n768976578 :   "(\<Psi>\<^sub>\<phi> forest) = (\<lambda>symbol2. psi (NODE symbol2 (children symbol2))) |`| rootSymbols" by auto
      have "\<And>symbol2 . (((psi (NODE symbol2 (children symbol2)))) = (((NODE symbol2 (psiF (children symbol2))))))" using psiDef psiF_def  by metis 
      have n76986876 : "\<And>symbol2 . (\<delta>\<^sub>\<tau>  (((NODE symbol2 (psiF (children symbol2))))) = (\<lambda> x.(symbol2#x)) |`| (pathsInForest (psiF (children symbol2)) |\<union>| (finsert [] fempty)))" using pathAlternateDef pathsInForest_def by fastforce
      have n546i878 : "\<And> child symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> heightForestBounded (\<Psi>\<^sub>\<phi> (children symbol)) n"
      proof (simp add : heightForestBounded_def)
        fix symbol
        assume n657587 : " symbol |\<in>| rootSymbols"
        have "\<And> t . t |\<in>| \<Psi>\<^sub>\<phi> (children symbol) \<Longrightarrow> height t \<le> n"
        proof -
          fix t
          assume n6568917 : "t |\<in>| \<Psi>\<^sub>\<phi> (children symbol)"
          from n768976578 n657587 have n65765687 : "psi (NODE symbol (children symbol)) |\<in>| (\<Psi>\<^sub>\<phi> forest)"
            by (simp add: fBexI) 
          from Suc.prems(1) heightForestBounded_def n65765687 have n656897 : "height (psi (NODE symbol (children symbol))) \<le> Suc n" by auto
          have n76687 : "psi (NODE symbol (children symbol)) = (NODE symbol (psiF (children symbol)))" using psiDef psiF_def   by metis 
          have "(psiF (children symbol)) = childrenSet (NODE symbol (psiF (children symbol)))" using childrenSet.simps by auto
          then have "t |\<in>| childrenSet (psi (NODE symbol (children symbol)))" using n76687 n6568917 by auto
          then show "height t \<le> n" using n656897   by (meson Suc_leI heightOfChild leD leI le_less_trans) 
        qed
        then show "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> (children symbol) \<longrightarrow> height t \<le> n" by auto
      qed
      then have n655876 : "\<And>  symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> (pathsInForest (psiF (children symbol))) = (pathsInForest ((children symbol)))" using Suc.hyps(1) by auto
      then have "\<And>  symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> (\<delta>\<^sub>\<tau>  (((NODE symbol (psiF (children symbol)))))) = (\<lambda> x.(symbol#x)) |`| (pathsInForest ((children symbol)) |\<union>| (finsert [] fempty))" using n76986876 by auto
          
          
      have n657867 : "\<And>  symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> pathsInForest (childrenWithSymbol symbol forest) =  (\<lambda> x.(symbol#x)) |`| (pathsInForest ((children symbol)) |\<union>| (finsert [] fempty))" 
      proof (simp add : children_def)
        fix symbol
        assume n65897 : "symbol |\<in>| rootSymbols"
        show " \<Pi>\<^sub>\<iota>\<^sub>\<phi> (childrenWithSymbol symbol forest) = finsert [symbol] (op # symbol |`| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))" 
        proof (simp add : pathsInForest_def)
          show "\<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest) = finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))"
          proof -
            have "\<And> path . path |\<in>| (\<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest)) = (path |\<in>| finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest))))"
            proof -
              fix path
              have n767987 : "\<And> tree . tree |\<in>| (childrenWithSymbol symbol forest) \<Longrightarrow> (root tree = symbol)" using childrenWithSymbol_def   by (smt Int_iff inf_fset2.rep_eq mem_Collect_eq notin_fset) 
              have "\<And>tree . path |\<in>| \<delta>\<^sub>\<tau> tree = (\<exists> tail. path = (root tree)#tail \<and> tail  |\<in>| (pathsInForest (childrenSet tree)) |\<union>| (finsert [] fempty))" using pathE by auto
              have " (path |\<in>| (\<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest))) = (\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> path |\<in>| \<delta>\<^sub>\<tau> tree)"                    by auto 
              also have "... = (\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> (\<exists> tail. path = (root tree)#tail \<and> tail  |\<in>| pathsInForest (childrenSet tree) |\<union>| (finsert [] fempty)))" using pathE by auto
              also have "... = (\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> (\<exists> tail. path = symbol#tail \<and> tail  |\<in>| pathsInForest (childrenSet tree) |\<union>| (finsert [] fempty)))" using n767987 by blast
              have "(path |\<in>| (finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))))  
= ( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> tail |\<in>| (\<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))))" by blast
              have n545786 : "( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> tail |\<in>| (\<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest))))) 
= ( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> (\<exists> tree. tree |\<in>| (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest)) \<and> tail |\<in>| \<delta>\<^sub>\<tau> tree)))"  by fastforce
              have n655687 : "\<And> tree. (tree |\<in>| (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest))) = (\<exists> upperTree . (upperTree |\<in>| ( childrenWithSymbol symbol forest) \<and> tree |\<in>| childrenSet upperTree))" by auto
              have n65876 : "(\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest)) \<Longrightarrow> ((\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> (\<exists> tail. path = symbol#tail \<and> tail  |\<in>| pathsInForest (childrenSet tree) |\<union>| (finsert [] fempty))) = 
(path = [symbol] \<or> (\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> (\<exists> tail. path = symbol#tail \<and> tail  |\<in>| pathsInForest (childrenSet tree)))))"                by blast  
              have n54645764 : "(\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest))" using n65897 rootSymbols_def childrenWithSymbol_def                by fastforce 
              from n545786 n655687 have n5466897 : "( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> (\<exists> tree. tree |\<in>| (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest)) \<and> tail |\<in>| \<delta>\<^sub>\<tau> tree))) = 
( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> (\<exists> tree. (\<exists> upperTree . (upperTree |\<in>| ( childrenWithSymbol symbol forest) \<and> tree |\<in>| childrenSet upperTree))  \<and> tail |\<in>| \<delta>\<^sub>\<tau> tree)))"                by (simp add: n655687)  
              from n65876  n54645764  n5466897  have "( path = [symbol] \<or> (\<exists> tail. path = symbol#tail \<and> (\<exists> tree. (\<exists> upperTree . (upperTree |\<in>| ( childrenWithSymbol symbol forest) \<and> tree |\<in>| childrenSet upperTree))  \<and> tail |\<in>| \<delta>\<^sub>\<tau> tree))) = 
                      (path = [symbol] \<or> (\<exists> tree. tree |\<in>| (childrenWithSymbol symbol forest) \<and> (\<exists> tail. path = symbol#tail \<and> tail  |\<in>| pathsInForest (childrenSet tree))))"
                by (metis pathsTreeForest)
              then show "path |\<in>| (\<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest)) = (path |\<in>| finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest))))"
                using \<open>(\<exists>tree. tree |\<in>| childrenWithSymbol symbol forest \<and> (\<exists>tail. path = root tree # tail \<and> tail |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (childrenSet tree) |\<union>| {|[]|})) = (\<exists>tree. tree |\<in>| childrenWithSymbol symbol forest \<and> (\<exists>tail. path = symbol # tail \<and> tail |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (childrenSet tree) |\<union>| {|[]|}))\<close> \<open>(path |\<in>| finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))) = (path = [symbol] \<or> (\<exists>tail. path = symbol # tail \<and> tail |\<in>| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest))))\<close> calculation n545786 n54645764 n5466897 n65876 by auto 
            qed
            then show "\<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest) = finsert [symbol] (op # symbol |`| \<Union>| (\<delta>\<^sub>\<tau> |`| \<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))" by auto
          qed
        qed
      qed
      have "((\<lambda>symbol2. \<delta>\<^sub>\<tau> (psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest))))) |`| (root |`| forest)) 
= (((\<lambda>symbol2. (\<lambda> x.(symbol2#x)) |`| (pathsInForest (psiF (children symbol2)) |\<union>| (finsert [] fempty)))) |`| (root |`| forest)) " using n76986876 
        using \<open>\<And>symbol2. psi (NODE symbol2 (children symbol2)) = NODE symbol2 (\<Psi>\<^sub>\<phi> (children symbol2))\<close> children_def n76986876 by auto 
          
      from n655876   have "(((\<lambda>symbol2. (\<lambda> x.(symbol2#x)) |`| (pathsInForest (psiF (children symbol2)) |\<union>| (finsert [] fempty)))) |`| (root |`| forest)) = 
          (((\<lambda>symbol2. (\<lambda> x.(symbol2#x)) |`| (pathsInForest ((children symbol2)) |\<union>| (finsert [] fempty)))) |`| (root |`| forest))"
        using rootSymbols_def by fastforce
          
          
      have "((\<lambda>symbol2. \<delta>\<^sub>\<tau> (psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest))))) |`| (root |`| forest)) = 
(((\<lambda>symbol2. (\<lambda> x.(symbol2#x)) |`| (pathsInForest ((children symbol2)) |\<union>| (finsert [] fempty)))) |`| (root |`| forest))"
        using \<open>(\<lambda>symbol2. \<delta>\<^sub>\<tau> (psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest))))) |`| root |`| forest = (\<lambda>symbol2. op # symbol2 |`| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (children symbol2)) |\<union>| {|[]|})) |`| root |`| forest\<close> \<open>(\<lambda>symbol2. op # symbol2 |`| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (children symbol2)) |\<union>| {|[]|})) |`| root |`| forest = (\<lambda>symbol2. op # symbol2 |`| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (children symbol2) |\<union>| {|[]|})) |`| root |`| forest\<close> by auto 
          
      from n657867 have "\<And>  symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> pathsInForest (childrenWithSymbol symbol forest) =  (\<lambda> x.(symbol#x)) |`| (pathsInForest ((children symbol)) |\<union>| (finsert [] fempty))" by auto
          
      then have "((\<lambda>symbol.  (pathsInForest (childrenWithSymbol symbol forest))) |`| rootSymbols) = ((\<lambda>symbol. (\<delta>\<^sub>\<tau> (psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest)))))) |`| rootSymbols)" using rootSymbols_def
        using \<open>(\<lambda>symbol2. \<delta>\<^sub>\<tau> (psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest))))) |`| root |`| forest = (\<lambda>symbol2. op # symbol2 |`| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (children symbol2) |\<union>| {|[]|})) |`| root |`| forest\<close> fimage_cong by force 
          
      have "\<Union>| (\<delta>\<^sub>\<tau> |`| forest) = (\<Union>| ((\<lambda>symbol.  (pathsInForest (childrenWithSymbol symbol forest))) |`| rootSymbols))"
      proof -
        have "forest = \<Union>| ((\<lambda>symbol.  ((childrenWithSymbol symbol forest))) |`| rootSymbols)"
        proof (simp add : childrenWithSymbol_def rootSymbols_def)
          
          show "forest = \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest)"
          proof -
            have "\<And>x . (x |\<in>| forest) = (x |\<in>| \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest))"
            proof
              fix x
              show "x |\<in>| forest \<Longrightarrow> x |\<in>| \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest)"
              proof -
                assume n765876 : " x |\<in>| forest"
                hence n76574 : "root x |\<in>| root |`| forest" by simp
                from n765876 have nt5434675 : "x |\<in>| (((inf_fset2 forest {child1. root child1 = root x})))"   by blast
                then show "x |\<in>| \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest)" using n76574 nt5434675
                  using n765876 by auto 
              qed
              show "x |\<in>| \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest) \<Longrightarrow> x |\<in>| forest"                by (smt ffUnionLemma comp_apply fimage.rep_eq finter_lower1 fset_mp imageE notin_fset)
            qed
            then show "forest = \<Union>| (((\<lambda>symbol. inf_fset2 forest {child1. root child1 = symbol}) \<circ> root) |`| forest)" by auto
          qed
        qed
        then show "\<Union>| (\<delta>\<^sub>\<tau> |`| forest) = \<Union>| ((\<lambda>symbol. \<Pi>\<^sub>\<iota>\<^sub>\<phi> (childrenWithSymbol symbol forest)) |`| rootSymbols)" 
        proof (simp add : pathsInForest_def)
          show "forest = \<Union>| ((\<lambda>symbol. childrenWithSymbol symbol forest) |`| rootSymbols) \<Longrightarrow> \<Union>| (\<delta>\<^sub>\<tau> |`| forest) = \<Union>| ((\<lambda>symbol. \<Union>| (\<delta>\<^sub>\<tau> |`| childrenWithSymbol symbol forest)) |`| rootSymbols)" using lemmaUnionUnion
            by fastforce 
        qed 
      qed
      then show "\<Union>| ((\<delta>\<^sub>\<tau> \<circ> ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 forest)))) \<circ> root)) |`| forest) = \<Union>| (\<delta>\<^sub>\<tau> |`| forest)"
        using \<open>(\<lambda>symbol. \<Pi>\<^sub>\<iota>\<^sub>\<phi> (childrenWithSymbol symbol forest)) |`| rootSymbols = (\<lambda>symbol. \<delta>\<^sub>\<tau> (psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol forest))))) |`| rootSymbols\<close> rootSymbols_def by auto 
    qed
  qed
qed
  
  
  
    
lemma psiPreservesPaths:
  "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> f) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (f)"
proof -
  have a2 : "\<exists>n . heightForestBounded (\<Psi>\<^sub>\<phi> f) n" proof (simp add : heightForestBounded_def)
    def maxHeight == "maxFset (height |`| (\<Psi>\<^sub>\<phi> f))"
    have "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> f \<longrightarrow> height t \<le> maxHeight" using maxHeight_def finiteMaxExists by simp
    then show "\<exists>n. \<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> f \<longrightarrow> height t \<le> n"  by auto
  qed
  from a2 psiPreservesPaths0  show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> f) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (f)" by auto
qed
  
  
  
  
  (* psi only depends on the pathset *)
  
lemma psiOnlyDependsOnPath0:
  shows "\<And> (otherForest1 :: abc tree fset) otherForest2 . (heightForestBounded (\<Psi>\<^sub>\<phi> otherForest1) n \<Longrightarrow> \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2) \<Longrightarrow> \<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2)"
proof (induct n)
  case 0
  from "0.prems"(1) have "\<Psi>\<^sub>\<phi> otherForest1  = fempty" using heightForestBounded_def height.simps tree.exhaust
  proof -
    have "\<forall>t. \<exists>a f. NODE (a::abc) f = t"
      by (metis tree.exhaust)
    then show ?thesis
      by (metis "0.prems"(1) Suc_eq_plus1_left bot.extremum_uniqueI bot_nat_def equalsffemptyI height.simps heightForestBounded_def old.nat.distinct(2))
  qed 
  hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = fempty" using pathsInForest_def by (simp add: pathsInForest_def ffUnion_empty) 
  hence "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2) = fempty"   by (simp add: "0.prems"(2)) 
  hence "\<Psi>\<^sub>\<phi> otherForest2 = fempty" using pathForestEmpty by auto
  then show ?case
    using \<open>\<Psi>\<^sub>\<phi> otherForest1 = {||}\<close> by auto 
next
  case (Suc n)
  from pathsInForest_def have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = \<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest1))" by auto
  from pathsInForest_def have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2) = \<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest2))" by auto
  have a1 : "\<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest1)) = \<Union>| (\<Pi> |`| (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) |`| root |`| otherForest1)" by (simp add : psiF_def)
  have a2 : "\<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest2)) = \<Union>| (\<Pi> |`| (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest2)))) |`| root |`| otherForest2)" by (simp add : psiF_def) 
  from Suc.prems(2) rootsPaths have "root |`| (\<Psi>\<^sub>\<phi>  otherForest1) = root |`| (\<Psi>\<^sub>\<phi> otherForest2)"   by (simp add: rootsPaths fsubset_antisym) 
  then have a3 : "root |`| otherForest1 = root |`| otherForest2" using rootsPsi by auto
  def rootSymbols == "root |`| otherForest1"
  from rootSymbols_def a1  have "\<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest1)) = \<Union>| (\<Pi> |`| (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) |`| rootSymbols)" by auto
  from psiF_def rootSymbols_def  have  n6565687 :   "(\<Psi>\<^sub>\<phi> otherForest1) = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) |`| rootSymbols" by auto
  from psiF_def rootSymbols_def a3  have  n6565687a :   "(\<Psi>\<^sub>\<phi> otherForest2) = (\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest2)))) |`| rootSymbols" by auto
  def children1 == "\<lambda> symbol.(\<Union>| (childrenSet |`| childrenWithSymbol (symbol :: abc) otherForest1))"
  def children2 == "\<lambda> symbol.(\<Union>| (childrenSet |`| childrenWithSymbol (symbol :: abc) otherForest2))"
  from children1_def  n6565687  have n768976578 :   "(\<Psi>\<^sub>\<phi> otherForest1) = (\<lambda>symbol2. psi (NODE symbol2 (children1 symbol2))) |`| rootSymbols" by auto
  from children1_def   have "\<And>symbol . (\<Pi> (psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol otherForest1))))) = (\<Pi> (psi (NODE symbol (children1 symbol))))" by auto
  from children2_def   have "\<And>symbol . (\<Pi> (psi (NODE symbol (\<Union>| (childrenSet |`| childrenWithSymbol symbol otherForest2))))) = (\<Pi> (psi (NODE symbol (children2 symbol))))" by auto
  from psiDef have "\<And>symbol . (\<Pi> (psi (NODE symbol (children1 symbol))) = (\<Pi> (NODE symbol ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (children1 symbol))))) |`| root |`| (children1 symbol)))))"
    by metis  
  from psiDef have "\<And>symbol . (\<Pi> (psi (NODE symbol (children2 symbol))) = (\<Pi> (NODE symbol ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 (children2 symbol))))) |`| root |`| (children2 symbol)))))"
    by metis
  have j1 :  "\<And>symbol . ((psi (NODE symbol (children1 symbol))) = ((NODE symbol ((psiF (children1 symbol))))))" by (metis psiDef psiF_def)          
  have j2 : "\<And>symbol . ((psi (NODE symbol (children2 symbol))) = ((NODE symbol ((psiF (children2 symbol))))))" by (metis psiDef psiF_def)   
  from \<Pi>_def have i1 : "\<And>symbol . (\<Pi> ((NODE symbol (psiF  (children1 symbol)))) = (\<lambda> x. symbol#x) |`| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children1 symbol))) |\<union>| (finsert [] fempty)))"  using pathsInForest_def by fastforce 
  from \<Pi>_def have i2 : "\<And>symbol . (\<Pi> ((NODE symbol (psiF  (children2 symbol)))) = (\<lambda> x. symbol#x) |`| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children2 symbol))) |\<union>| (finsert [] fempty)))"  using pathsInForest_def by fastforce 
  have n7566896 : "\<And>symbol . (\<Psi>\<^sub>\<phi> (children1 symbol)) = \<Psi>\<^sub>\<phi> (\<Union>| (childrenSet |`| childrenWithSymbol (symbol :: abc) otherForest1))" using children1_def by auto
  have n7566896a : "\<And>symbol . (\<Psi>\<^sub>\<phi> (children2 symbol)) = \<Psi>\<^sub>\<phi> (\<Union>| (childrenSet |`| childrenWithSymbol (symbol :: abc) otherForest2))" using children2_def by auto
  have n546i878 : "\<And> child symbol .  symbol |\<in>| rootSymbols \<Longrightarrow> heightForestBounded (\<Psi>\<^sub>\<phi> (children1 symbol)) n"
  proof (simp add : heightForestBounded_def)
    fix symbol
    assume n657587 : " symbol |\<in>| rootSymbols"
    have "\<And> t . t |\<in>| \<Psi>\<^sub>\<phi> (children1 symbol) \<Longrightarrow> height t \<le> n"
    proof -
      fix t
      assume n6568917 : "t |\<in>| \<Psi>\<^sub>\<phi> (children1 symbol)"
      from n768976578 n657587 have n65765687 : "psi (NODE symbol (children1 symbol)) |\<in>| (\<Psi>\<^sub>\<phi> otherForest1)" by auto
      from Suc.prems(1) heightForestBounded_def n65765687 have n656897 : "height (psi (NODE symbol (children1 symbol))) \<le> Suc n" by auto
      have n76687 : "psi (NODE symbol (children1 symbol)) = (NODE symbol (psiF (children1 symbol)))" using psiDef psiF_def   by metis 
      have "(psiF (children1 symbol)) = childrenSet (NODE symbol (psiF (children1 symbol)))" using childrenSet.simps by auto
      then have "t |\<in>| childrenSet (psi (NODE symbol (children1 symbol)))" using n76687 n6568917 by auto
      then show "height t \<le> n" using n656897   by (meson Suc_leI heightOfChild leD leI le_less_trans) 
    qed
    then show "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> (children1 symbol) \<longrightarrow> height t \<le> n" by auto
  qed
  have "\<And>symbol . symbol |\<in>| rootSymbols \<Longrightarrow> (\<Pi> (psi (NODE symbol (children1 symbol))) = \<Pi> (psi (NODE symbol (children2 symbol))))" 
  proof -
    fix symbol
    assume n76987 : "symbol |\<in>| rootSymbols"
    from Suc.prems(2) have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2) " by auto
    then have "\<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest1)) = \<Union>| (\<Pi> |`| (\<Psi>\<^sub>\<phi> otherForest2))" by (simp add:pathsInForest_def )
    have n7686875476 : "\<And>x . (x |\<in>| (\<Pi> (psi (NODE symbol (children1 symbol)))) \<Longrightarrow> (x |\<in>| \<Pi> (psi (NODE symbol (children2 symbol)))))"
    proof -
      fix x
      assume n656897 : "x |\<in>| (\<Pi> (psi (NODE symbol (children1 symbol))))"
      hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1)" using n76987 n7566896 pathsInForest_def   using children1_def n6565687 by fastforce 
      hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2)"
        by (simp add: Suc.prems(2)) 
      then obtain symbol2 where n545786 : "x |\<in>| (\<Pi> (psi (NODE symbol2 (children2 symbol2))))" using n76987 n7566896a pathsInForest_def  by (smt ffUnionLemma a2 children2_def fimageE) 
      from n656897 have n1 : "hd x = symbol" using \<Pi>.simps
        using j1 by auto 
      from n545786 have n2 : "hd x = symbol2" using \<Pi>.simps 
        using j2 by auto 
      from n1 n2 have "symbol = symbol2" by auto
      then show "(x |\<in>| \<Pi> (psi (NODE symbol (children2 symbol))))" using n545786 by auto
    qed
    have n7686875476a : "\<And>x . (x |\<in>| (\<Pi> (psi (NODE symbol (children2 symbol)))) \<Longrightarrow> (x |\<in>| \<Pi> (psi (NODE symbol (children1 symbol)))))"
    proof -
      fix x
      assume n656897 : "x |\<in>| (\<Pi> (psi (NODE symbol (children2 symbol))))"
      hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2)" using n76987 n7566896a pathsInForest_def   using children2_def n6565687a by fastforce 
      hence "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1)"
        by (simp add: Suc.prems(2)) 
      then obtain symbol2 where n545786 : "x |\<in>| (\<Pi> (psi (NODE symbol2 (children1 symbol2))))" using n76987 n7566896 pathsInForest_def    by (smt ffUnionLemma a1 children1_def fimageE) 
      from n656897 have n1 : "hd x = symbol" using \<Pi>.simps
        using j2 by auto 
      from n545786 have n2 : "hd x = symbol2" using \<Pi>.simps 
        using j1 by auto 
      from n1 n2 have "symbol = symbol2" by auto
      then show "(x |\<in>| \<Pi> (psi (NODE symbol (children1 symbol))))" using n545786 by auto
    qed
    from n7686875476a n7686875476 show "\<delta>\<^sub>\<tau> (psi (NODE symbol (children1 symbol))) = \<delta>\<^sub>\<tau> (psi (NODE symbol (children2 symbol)))" by auto
  qed
  then have "\<And>symbol . symbol |\<in>| rootSymbols \<Longrightarrow> ((\<lambda> x. symbol#x) |`| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children1 symbol))) |\<union>| (finsert [] fempty)) = (\<lambda> x. symbol#x) |`| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children2 symbol))) |\<union>| (finsert [] fempty)))" using i1 i2 j1 j2 by metis
  then have n65786 : "\<And>symbol . symbol |\<in>| rootSymbols \<Longrightarrow> (((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children1 symbol))) |\<union>| (finsert [] fempty)) = ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children2 symbol))) |\<union>| (finsert [] fempty)))" using suffixSets   by blast 
  have "\<And>symbol . symbol |\<in>| rootSymbols \<Longrightarrow> (((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children1 symbol))) ) = ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (psiF  (children2 symbol))) ))"  using n65786 pathsContainment
    by (simp add: pathsContainment fsubset_antisym) 
  then have "\<And>symbol . symbol |\<in>| rootSymbols \<Longrightarrow> ((( (psiF  (children1 symbol))) ) = (( (psiF  (children2 symbol))) ))" using n546i878 Suc.hyps by auto
  show "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2" 
  proof (simp add : psiF_def)
    have "\<And> symbol2. symbol2 |\<in>| rootSymbols \<Longrightarrow> (((psi (NODE symbol2 (children1 symbol2))) ) = ((psi (NODE symbol2 (children2 symbol2))) ))"  by (simp add: \<open>\<And>symbol. symbol |\<in>| rootSymbols \<Longrightarrow> \<Psi>\<^sub>\<phi> (children1 symbol) = \<Psi>\<^sub>\<phi> (children2 symbol)\<close> j1 j2)   
    hence " ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) |`| rootSymbols) = ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest2)))) |`| rootSymbols)"  using children1_def children2_def
      by force 
    hence " ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) |`| (root |`| otherForest1)) =  ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest2)))) |`| (root |`| otherForest2))" using rootSymbols_def a3 by auto
    then show " ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest1)))) \<circ> root) |`| otherForest1 =  ((\<lambda>symbol2. psi (NODE symbol2 (\<Union>| (childrenSet |`| childrenWithSymbol symbol2 otherForest2)))) \<circ> root) |`| otherForest2" by auto
  qed
qed
  
  
lemma psiOnlyDependsOnPath1:
  assumes "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2)" 
  shows "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2"
proof -
  have a2 : "\<exists>n . heightForestBounded (\<Psi>\<^sub>\<phi> otherForest1) n" proof (simp add : heightForestBounded_def)
    def maxHeight == "maxFset (height |`| (\<Psi>\<^sub>\<phi> otherForest1))"
    have "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<longrightarrow> height t \<le> maxHeight" using maxHeight_def finiteMaxExists by simp
    then show "\<exists>n. \<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<longrightarrow> height t \<le> n"  by auto
  qed
  from a2 psiOnlyDependsOnPath0 assms show "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2" by auto
qed
  
    
lemma psiOnlyDependsOnPath:
  assumes "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (otherForest1) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (otherForest2)" 
  shows "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2"
proof -
  from assms have a1 : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest1) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> otherForest2)" using psiPreservesPaths by auto
  have a2 : "\<exists>n . heightForestBounded (\<Psi>\<^sub>\<phi> otherForest1) n" proof (simp add : heightForestBounded_def)
    def maxHeight == "maxFset (height |`| (\<Psi>\<^sub>\<phi> otherForest1))"
    have "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<longrightarrow> height t \<le> maxHeight" using maxHeight_def finiteMaxExists by simp
    then show "\<exists>n. \<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> otherForest1 \<longrightarrow> height t \<le> n"  by auto
  qed
  from a1 a2 psiOnlyDependsOnPath0 show "\<Psi>\<^sub>\<phi> otherForest1 = \<Psi>\<^sub>\<phi> otherForest2" by auto
qed
  
  
  
lemma oplusRoots :
  assumes "\<And>rule \<ii>. rule |\<in>| \<R> \<ii> \<Longrightarrow> symbol rule = \<alpha>"
  shows "forest \<in> \<Psi>\<^sub>\<Oplus>\<^sub>\<rho> (\<R> \<aa>\<^sub>1) (\<R> \<aa>\<^sub>2) \<Longrightarrow> tr \<in> fset forest \<Longrightarrow> root tr = \<alpha>"
proof (simp add : dist_intersectionLanguageOplusRules_def)
  show "forest \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) \<and> forest \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2 |`| \<R> \<aa>\<^sub>2) \<Longrightarrow> tr \<in> fset forest \<Longrightarrow> root tr = \<alpha>"
  proof -
    assume "forest \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) \<and> forest \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>2 |`| \<R> \<aa>\<^sub>2)"
    hence "forest \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) " by auto
    then obtain oldForest where n875654 : "forest = \<Psi>\<^sub>\<phi> oldForest" and n86654 : "oldForest \<in> \<Oplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) " by auto
    assume n865654 : "tr \<in> fset forest"
    from psiF_def n875654 n865654 obtain symbol1 where n8757 : "symbol1 |\<in>| root |`| oldForest" and n897564 : "tr = psi (NODE symbol1 (\<Union>| (childrenSet |`| childrenWithSymbol symbol1 oldForest)))" using notin_fset by fastforce  
    from n8757 obtain oldTree where n754543 : "root oldTree = symbol1" and n6t435 : "oldTree |\<in>| oldForest" by auto
    from bigoplusForests_def have n865654 : "oldForest \<in> \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1)" using n86654 by auto
    from biguplusForests_def n6t435 n865654 obtain lang subforest rule where n876765 : "lang |\<in>| (\<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1 |`| \<R> \<aa>\<^sub>1) \<and> ( oldTree |\<in>| subforest \<and> subforest |\<subseteq>| oldForest \<and> subforest \<in> lang)"
      by (smt mem_Collect_eq) 
    then obtain rule where n8765654 : "rule |\<in>| \<R> \<aa>\<^sub>1" and "lang = \<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1  rule" by auto
    hence "subforest \<in> \<L>\<^sub>\<phi>\<^sub>\<rho> \<A>\<^sub>1  rule" using n876765 by auto
    hence "oldTree \<in> \<L>\<^sub>\<tau>\<^sub>\<rho> \<A>\<^sub>1  rule"      by (simp add: forest_language_for_rule_def language_for_rule_def n876765)
    hence "root oldTree = (symbol rule)"          by (metis \<A>.simps(1) rootRule) 
    hence "root oldTree = \<alpha>" using assms(1) n8765654 by auto
    hence "symbol1 = \<alpha>" using n754543 by auto
    then show "root tr = \<alpha>" using n897564 root.simps      by (simp add: psiRoot) 
  qed
qed
  
  
    
lemma ffUnionLemma :
  fixes x a
  shows "(x |\<in>| \<Union>| a) = (\<exists> b. (b |\<in>| a \<and> x |\<in>| b))"
  by auto
    
            
    
  
lemma UnionPathsInOut : "\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| languages) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Uplus> (languages))"
proof -
  have "\<And>x . (x \<in> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| languages)) = (x \<in> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Uplus> (languages))))"
  proof (simp add : biguplusForestsD_def biguplusForests_def)
    show "\<And>x. (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))) =
         (x \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))})"
    proof -
      fix x
      have "(x \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))})
= (\<exists> forest . (x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and>  (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))))" by auto
      have "(\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))
\<Longrightarrow> (\<exists> forest . (x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and>  (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))))"
      proof -
        assume a1 : "\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))"
        hence "\<forall>tr.  (\<exists>lang. (tr |\<in>| x \<longrightarrow> (lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))))" by metis
            
            
        def isGood == "\<lambda> tr language. (tr |\<in>|x \<longrightarrow> language |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> language))"
        from a1 isGood_def have "\<And>tr . \<exists> language . isGood tr language" by auto
        then obtain chosenLanguage where "\<And>tr . (isGood tr (chosenLanguage tr))" using dependentChoice by auto
        hence "\<And> tr . tr |\<in>|x \<Longrightarrow> ((chosenLanguage tr) |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> (chosenLanguage tr)))" using isGood_def by auto
        hence n655687 : "\<And> tr . tr |\<in>|x \<Longrightarrow> ((chosenLanguage tr) |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages)" and n76876 : "\<And> tr . tr |\<in>|x \<Longrightarrow> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> (chosenLanguage tr))" by auto
            
            
        def isGood2 == "\<lambda> tr subforest . (tr |\<in>|x  \<longrightarrow> ( tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> (chosenLanguage tr)))"
        hence "\<And> tr . (\<exists> subforest . isGood2 tr subforest)" using n76876 by auto
        then obtain subForestForTr where "\<And> tr . (isGood2 tr (subForestForTr tr))" using dependentChoice by auto
        hence n65453 : "\<And>tr . tr |\<in>|x \<Longrightarrow> ( tr |\<in>| (subForestForTr tr) \<and> (subForestForTr tr) |\<subseteq>| x \<and> (subForestForTr tr) \<in> (chosenLanguage tr))" using isGood2_def by auto
            
            
        from n655687 have "\<And> tr . tr |\<in>|x \<Longrightarrow> (\<exists> language . (language |\<in>| languages \<and>  (chosenLanguage tr) = (op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) language))"  by blast
        hence "\<And> tr . tr |\<in>|x \<Longrightarrow> (\<exists> language . (language |\<in>| languages \<and>   (subForestForTr tr) \<in> (op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) language))" using n65453 by metis
        hence n765765 : "\<And> tr . tr |\<in>|x \<Longrightarrow> (\<exists> originalForest . (\<exists> language . (language |\<in>| languages \<and> originalForest \<in> language \<and> (subForestForTr tr) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> originalForest)))" by blast
        def isGood3 == "\<lambda> tr originalForest . (tr |\<in>|x \<longrightarrow> (\<exists> language . (language |\<in>| languages \<and> originalForest \<in> language \<and> (subForestForTr tr) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> originalForest)))"
        from n765765 isGood3_def have "\<And> tr . \<exists> originalForest . isGood3 tr originalForest" by auto
        then obtain originalForestForTr where "\<And> tr . isGood3 tr (originalForestForTr tr)" using dependentChoice by auto
        hence n655687674 : "\<And> tr . tr |\<in>|x \<Longrightarrow> (\<exists> language . (language |\<in>| languages \<and> (originalForestForTr tr) \<in> language \<and> (subForestForTr tr) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr)))" using isGood3_def by auto
        def fullForest == "\<Union>| (originalForestForTr |`| x)"
        have "x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> fullForest" 
        proof (simp add : fullForest_def)
          show "x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (originalForestForTr |`| x))"
          proof
            show " x |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (originalForestForTr |`| x))"
            proof
              fix tr
              assume j1 : "tr |\<in>| x"
              hence n654r764 : "tr |\<in>| (subForestForTr tr)" using n65453 by auto
              from n655687674 j1   have "(subForestForTr tr) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr)" by auto
              hence "tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr)" using n654r764 by auto
              then   show "tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (originalForestForTr |`| x))"  using j1
                by (meson ffUnionLemma fimage_eqI pathsTreeForest)  
            qed
            show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (originalForestForTr |`| x)) |\<subseteq>| x" 
            proof 
              fix tr
              assume "tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (originalForestForTr |`| x))"
              then obtain tr2 where n6t43432 : "tr2 |\<in>| x" and "tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr2)"                 by (smt ffUnionLemma fimageE pathsTreeForest) 
              from n65453 n655687674 n6t43432 have "(subForestForTr tr2) |\<subseteq>| x" by blast
              from n65453 n655687674 n6t43432 have  "(subForestForTr tr2) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr2)" by blast
              show "tr |\<in>| x"              using \<open>subForestForTr tr2 |\<subseteq>| x\<close> \<open>tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr2)\<close> n655687674 n6t43432 by fastforce 
            qed
          qed
        qed
        have "\<And> tr. tr |\<in>| fullForest \<Longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| fullForest \<and> subforest \<in> lang))"
        proof -
          fix tr
          assume "tr |\<in>| fullForest"
          then obtain tr2 where n654543 :  "tr2 |\<in>| x" and "tr |\<in>| originalForestForTr tr2" using fullForest_def by auto
          then have ny654543 : " (\<exists> language . (language |\<in>| languages \<and> (tr |\<in>| originalForestForTr tr2) \<and> (originalForestForTr tr2) \<in> language \<and> (subForestForTr tr2) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (originalForestForTr tr2)))" using   n655687674 by auto
          from fullForest_def n654543  have "originalForestForTr tr2 |\<subseteq>| fullForest" by auto
          then show "\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| fullForest \<and> subforest \<in> lang)" using ny654543 by auto
        qed
        show "\<exists>forest. x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and> (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))"
          using \<open>\<And>tr. tr |\<in>| fullForest \<Longrightarrow> \<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| fullForest \<and> subforest \<in> lang)\<close> \<open>x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> fullForest\<close> by blast 
      qed
      have "(\<exists> forest . (x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and>  (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))))) 
           \<Longrightarrow> (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))"
      proof -
        assume "(\<exists> forest . (x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and>  (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))))"
        then obtain forest where n653543 : "x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and>  (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))" by auto
        have "\<And> tr. tr |\<in>| x \<Longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))"
        proof -
          fix tr
          assume n653654543 : "tr |\<in>| x"
          from n653543 have n65543 : "(\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))" by auto
          from n653543 have ny64543 : "x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest" by blast
          then obtain tree where no86654  : "tree |\<in>| forest" and n7u6453 : "tr |\<in>| \<Pi> tree" using pathsInForest_def n653654543 ffUnionLemma fimageE pathsTreeForest
            by metis 
          from n65543 no86654 have "(\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tree |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))" by auto
          hence "(\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tree |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest \<in> lang))" by auto
          hence "(\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tree |\<in>| subforest \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest \<in> lang))" using pathsInForest_def fimageE   by (smt fset_mp fsubsetI pathsTreeForest) 
              
          hence "(\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest |\<subseteq>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and> \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest \<in> lang))" using n7u6453 pathsInForest_def fimageE   by (smt fset_mp fsubsetI pathsTreeForest) 
          then show "(\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))" using ny64543 by auto
        qed
        then show "(\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))" by auto
      qed
      show "(\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))) =
         (x \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))})"
        using \<open>\<exists>forest. x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and> (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))) \<Longrightarrow> \<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))\<close> \<open>\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)) \<Longrightarrow> \<exists>forest. x = \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest \<and> (\<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| languages \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang)))\<close> by blast 
    qed
  qed
  then show ?thesis by auto
qed
  
  
lemma nu67543433 : "\<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| languages) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (languages))" 
using UnionPathsInOut psiPreservesPaths
  by (metis (full_types) image_cong image_image pathsInForest_def) 
    
    
(*    lemma nu67543433b : "\<Oplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi>) |`| languages) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Oplus> (languages))" 
using UnionPathsInOut psiPreservesPaths
  by (metis (full_types) image_cong image_image pathsInForest_def) *)
    
lemma psiPiAddition : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (forest1 |\<union>| forest2)) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ( (\<Psi>\<^sub>\<phi> forest2) |\<union>| (\<Psi>\<^sub>\<phi> forest1))"
proof -
  have "\<And>f. \<Union>| (\<delta>\<^sub>\<tau> |`| \<Psi>\<^sub>\<phi> f) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> f"        by (metis (no_types) pathsInForest_def psiPreservesPaths)
  then show ?thesis        by (simp add: fimage_funion pathsInForest_def sup_commute)
qed  
    
lemma pathsUnionCommute : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Union>| forests)) = (\<Union>|  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  |`| forests))"
proof -
(*  have "\<And>x . (x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Union>| forests))) = (\<exists> tree . tree |\<in>| ((\<Union>| forests)) \<and> x |\<in>| \<Pi> tree)" using pathsInForest_def ffUnionLemma    by (metis pathsTreeForest)  
  have "\<And> x . (\<exists> tree . tree |\<in>| ((\<Union>| forests)) \<and> x |\<in>| \<Pi> tree) = (\<exists> tree forest . forest |\<in>| forests \<and> tree |\<in>| forest \<and> x |\<in>| \<Pi> tree)" using ffUnionLemma by auto*)
  have "\<And>x. (x |\<in>| (\<Union>|  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  |`| forests))) = (\<exists>  forest . forest |\<in>| forests \<and>  x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest)" using ffUnionLemma        by auto 
  hence "\<And>x. (x |\<in>| (\<Union>|  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  |`| forests))) = (\<exists> tree forest . forest |\<in>| forests \<and> tree |\<in>| forest \<and> x |\<in>| \<Pi> tree)" using pathsInForest_def ffUnionLemma    by (metis pathsTreeForest)  
  hence "\<And>x . (x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Union>| forests)) = (x |\<in>| (\<Union>|  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  |`| forests))))"    by (meson ffUnionLemma pathsTreeForest) 
  then show   "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Union>| forests)) = (\<Union>|  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  |`| forests))"  by auto
qed
  
      
lemma psiPiAdditionArbitrary : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<Union>| forests)) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>|  (\<Psi>\<^sub>\<phi> |`| forests))" 
proof -
  have   "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<Union>| forests)) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> ((\<Union>| forests))" using psiPreservesPaths by auto
  also have "... = ((\<Union>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| forests)))" using pathsUnionCommute by auto
  also have "... = ((\<Union>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| (\<Psi>\<^sub>\<phi> |`| forests))))" using psiPreservesPaths by auto
  also have "... = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| ( \<Psi>\<^sub>\<phi> |`| forests)))" using pathsUnionCommute by blast
  show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<Union>| forests)) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>|  (\<Psi>\<^sub>\<phi> |`| forests))" using \<open>\<Union>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> |`| \<Psi>\<^sub>\<phi> |`| forests) = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| (\<Psi>\<^sub>\<phi> |`| forests))\<close> calculation by auto 
qed
  
    
lemma psiPiIntersection : "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language1 \<inter> \<Psi>\<^sub>\<phi> `language2) = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language1)) \<inter> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language2))"
proof
  show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language1 \<inter> \<Psi>\<^sub>\<phi> `language2) \<subseteq> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language1)) \<inter> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language2))"
    by (simp add: image_mono) 
  show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` language1 \<inter> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` language2 \<subseteq> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` language1 \<inter> \<Psi>\<^sub>\<phi> ` language2)" using  psiOnlyDependsOnPath
    by (smt Int_iff image_iff inf_le1 psiOnlyDependsOnPath1 subsetCE subsetI subset_imageE) 
qed
  
  
lemma psiDeltaPsi : "\<delta>\<^sub>\<phi> ` (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma> Sa1 Sa2) = (\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta> Sa1 Sa2)" 
proof (simp add :\<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>_def \<Psi>\<^sub>\<Sigma>\<^sub>\<sigma>\<^sub>\<delta>_def)
  have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)) = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1))) \<inter> (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)))"
  proof
    show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)) \<subseteq> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)"      by (simp add: image_mono) 
    show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2) \<subseteq> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2))" using psiPiIntersection by auto
  qed
  then show "\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1 |`| Sa1) \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> (\<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2 |`| Sa2)) = \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>1) |`| Sa1) \<inter> \<Uplus>\<^sub>\<delta> ((op ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> \<L>\<^sub>\<phi>\<^sub>\<sigma> \<A>\<^sub>2) |`| Sa2)" using nu67543433    by (metis fset.map_comp) 
qed
  
  
  
    

lemma unionPaths :
  shows "\<Pi>\<^sub>\<iota>\<^sub>\<phi> (a |\<union>| b) = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> a) |\<union>| (\<Pi>\<^sub>\<iota>\<^sub>\<phi> b)"
    by (simp add: pathsInForest_def fimage_funion) 
    
  
lemma closedAndP : 
assumes "closedUnderPlus l"
shows "closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
proof -
  show "closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"  using  closedUnderPlusD_def closedUnderPlus_def CombinatoricsBackground.plus_def plusD_def unionPaths
  proof -
    obtain ff :: "'a list fset set \<Rightarrow> 'a list fset" and ffa :: "'a list fset set \<Rightarrow> 'a list fset" where
        f1: "\<forall>F. ff F \<in> F \<and> ffa F \<in> F \<and> plusD (ff F) (ffa F) \<notin> F \<or> closedUnderPlusD F"
      using closedUnderPlusD_def by moura
    obtain ffb :: "'a list fset \<Rightarrow> ('a tree fset \<Rightarrow> 'a list fset) \<Rightarrow> 'a tree fset set \<Rightarrow> 'a tree fset" where
      f2: "\<forall>f fa F. (f \<notin> fa ` F \<or> ffb f fa F \<in> F \<and> fa (ffb f fa F) = f) \<and> ((\<forall>fb. fb \<notin> F \<or> fa fb \<noteq> f) \<or> f \<in> fa ` F)"
      by moura
    have f3: "\<forall>f F fa. (fa::'a tree fset) |\<union>| f \<in> F \<or> f \<notin> F \<or> fa \<notin> F \<or> \<not> closedUnderPlus F"
      by (metis closedUnderPlus_def plus_def)
    { assume "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) = ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (ffb (ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)) \<Pi>\<^sub>\<iota>\<^sub>\<phi> l)"
      moreover
      { assume "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) = ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> (ffb (ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)) \<Pi>\<^sub>\<iota>\<^sub>\<phi> l) \<and> ffb (ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)) \<Pi>\<^sub>\<iota>\<^sub>\<phi> l \<in> l"
        moreover
        { assume "\<exists>f. ffb (ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)) \<Pi>\<^sub>\<iota>\<^sub>\<phi> l |\<union>| f \<in> l \<and> ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f = ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
          moreover
          { assume "\<exists>f. ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) |\<union>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> f \<noteq> \<Pi>\<^sub>\<iota>\<^sub>\<phi> (ffb (ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)) \<Pi>\<^sub>\<iota>\<^sub>\<phi> l |\<union>| f)"
            then have "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<notin> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l"
              using f2 by (metis (no_types) unionPaths) }
          ultimately have "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<longrightarrow> closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
            using f2 f1 by (metis (no_types) plusD_def) }
        ultimately have "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<and> ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<longrightarrow> closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
          using f3 assms by blast }
      ultimately have "ff (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<and> ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<longrightarrow> closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
        using f2 by meson
      then have "ffa (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l) \<in> \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l \<longrightarrow> closedUnderPlusD (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` l)"
        using f1 by meson }
    then show ?thesis
      using f2 f1 by (metis (no_types))
  qed
qed
  
  
  
lemma zInter : "\<Z>\<^sub>\<phi>\<^sub>F n (A \<inter> B) = (\<Z>\<^sub>\<phi>\<^sub>F n A) \<inter> (\<Z>\<^sub>\<phi>\<^sub>F n B)"        using \<Z>\<^sub>\<phi>\<^sub>F_def by auto 
lemma "\<Z>\<^sub>\<phi>\<^sub>F n (A \<union> B) = (\<Z>\<^sub>\<phi>\<^sub>F n A) \<union> (\<Z>\<^sub>\<phi>\<^sub>F n B)"   using \<Z>\<^sub>\<phi>\<^sub>F_def by auto 
    
lemma "\<Z>\<^sub>\<phi>\<^sub>F n (\<Uplus> A) = \<Uplus> ((\<Z>\<^sub>\<phi>\<^sub>F n) |`| A)"
proof -
  have "\<And>x . ((x \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Uplus> A)) = (x \<in> \<Uplus> ((\<Z>\<^sub>\<phi>\<^sub>F n) |`| A)))" 
  proof (simp add : biguplusForests_def)
    show "\<And>x. (x \<in> \<Z>\<^sub>\<phi>\<^sub>F n {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))}) =
         (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| \<Z>\<^sub>\<phi>\<^sub>F n |`| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))"
    proof -
      have a1 : "\<And> x tr . (\<exists>lang. lang |\<in>| \<Z>\<^sub>\<phi>\<^sub>F n |`| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)) 
              = (\<exists>lang0. lang0 |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang0))"        by auto 
      hence a2 : "\<And>x . ((\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| \<Z>\<^sub>\<phi>\<^sub>F n |`| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))) = 
(\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang0. lang0 |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang0))))" by auto
      
      have "\<And>x . (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang0. lang0 |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang0)))
= (x \<in> \<Z>\<^sub>\<phi>\<^sub>F n {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))})"
      proof (simp add : \<Z>\<^sub>\<phi>\<^sub>F_def)
        show "\<And>x. (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang0. lang0 |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang0 \<and> (\<forall>t. t |\<in>| subforest \<longrightarrow> height t \<le> n)))) =
         ((\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang))) \<and> (\<forall>t. t |\<in>| x \<longrightarrow> height t \<le> n))"          by (meson fset_mp)
      qed
      then show "\<And>x. (x \<in> \<Z>\<^sub>\<phi>\<^sub>F n {forest. \<forall>tr. tr |\<in>| forest \<longrightarrow> (\<exists>lang. lang |\<in>| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| forest \<and> subforest \<in> lang))}) =
         (\<forall>tr. tr |\<in>| x \<longrightarrow> (\<exists>lang. lang |\<in>| \<Z>\<^sub>\<phi>\<^sub>F n |`| A \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| x \<and> subforest \<in> lang)))"  using a1 a2 by simp
    qed
  qed
  then show "\<Z>\<^sub>\<phi>\<^sub>F n (\<Uplus> A) = \<Uplus> (\<Z>\<^sub>\<phi>\<^sub>F n |`| A)" by auto
qed
  
        
lemma psiBoundedPreserved : "(a |\<in>| (boundedForests n)) = ((\<Psi>\<^sub>\<phi> a) |\<in>| (boundedForests n))"
  using heightBoundedPaths heightOnlyDependsOnPaths  using psiPreservesPaths by blast 
    
  
    
    
lemma zPsiCommute : "\<Psi>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n) A) = (\<Z>\<^sub>\<phi>\<^sub>F n) (\<Psi>\<^sub>\<phi> ` A)"
proof 
  show "\<Psi>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n A \<subseteq> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` A)" using psiBoundedPreserved \<Z>\<^sub>\<phi>\<^sub>F_def restrictionIsFiniteForests
    by (smt Int_iff image_eqI image_subsetI notin_fset) 
  show "\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` A) \<subseteq> \<Psi>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n A "  using psiBoundedPreserved \<Z>\<^sub>\<phi>\<^sub>F_def restrictionIsFiniteForests
    by (smt IntD2 IntI Int_commute image_iff notin_fset subsetI) 
qed
  
    
lemma piLangSum :
  fixes f lang
  assumes "f \<in> fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` lang)"
  shows "f \<subseteq> \<Pi>\<^sub>\<phi> (lang)"
  using pathsForForestLanguage_def
  by (smt assms imageE mem_Collect_eq notin_fset subsetI) 
    
    
lemma unionPathsCommute : "(\<Union> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` lang))) = ( ( (\<Pi>\<^sub>\<tau> (\<Union> (fset ` (lang))))))" 
proof 
  show "UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` lang) fset \<subseteq> \<Pi>\<^sub>\<tau> (UNION lang fset)" using pathsForTreeLanguage_def    by (smt Sup_le_iff Sup_upper imageE image_eqI pathsTreeLangMonotone piFset) 
  show "\<Pi>\<^sub>\<tau> (UNION lang fset) \<subseteq> UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` lang) fset " using pathsForTreeLanguage_def   pathsTreeLangMonotone piFset    by (smt Collect_mono Union_eq Union_iff bex_imageD image_eqI notin_fset pathsTreeForest) 
qed
  
lemma pathsTreeSetForest : "x \<in> fset ` lang \<Longrightarrow> \<Pi>\<^sub>\<tau> x \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` lang))" using pathsForTreeLanguage_def pathsInForest_def  using piFset by fastforce 
    
lemma lengthInRestriction :
  fixes path
  assumes " path \<in> (\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n language))"
  shows " length path \<le> n"
proof -
  from assms(1) obtain forest where n0 : "path |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest" and n1 : "forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n language)" using pathsForForestLanguage_def by blast
  then show "length path \<le> n"  using heightBoundedPaths heightOnlyDependsOnPaths \<Z>\<^sub>\<phi>\<^sub>F_def    by (metis (mono_tags, lifting) Int_iff fimage_eqI finiteMaxExists(1) le_trans mem_Collect_eq pathsTreeForest)
qed
  
  
lemma "{p. \<exists>t\<in>language. p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t} = {p. \<exists>t\<in>language. \<exists> tree \<in> (fset t) . p |\<in>| \<Pi> tree}" using pathsInForest_def notin_fset ffUnionLemma
  by (smt Collect_cong pathsTreeForest) 
    
lemma lengthHeightForests : 
  assumes "\<And>path .  path \<in> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> g) \<Longrightarrow> length path \<le> n"
  shows "\<And>tree. tree \<in> fset g \<Longrightarrow> height tree \<le> n"
  using heightOnlyDependsOnPaths pathsInForest_def
  by (metis (no_types, lifting) assms eq_iff fimageE finiteMaxExists(2) finiteMaxExists(3) le_0_eq nat_le_linear notin_fset pathsTreeForest) 
    
lemma    psiBoundedPreserved2 :
  assumes  "\<And> t. t |\<in>| forest \<Longrightarrow> height t \<le> n"         
  shows "\<And>t. t |\<in>| \<Psi>\<^sub>\<phi> forest \<Longrightarrow> height t \<le> n" 
proof -
  fix t :: "abc tree"
  assume a1: "t |\<in>| \<Psi>\<^sub>\<phi> forest"
  obtain aas :: "nat \<Rightarrow> abc tree fset \<Rightarrow> abc list" where
    f2: "\<forall>x1 x2. (\<exists>v3. v3 \<in> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> x2) \<and> \<not> length v3 \<le> x1) = (aas x1 x2 \<in> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> x2) \<and> \<not> length (aas x1 x2) \<le> x1)"
    by moura
  have "\<forall>t f. ((t::abc tree) |\<in>| f) = (t \<in> fset f)"
    by (metis notin_fset)
  then have f3: "t \<in> fset (\<Psi>\<^sub>\<phi> forest)"
    using a1 by metis
  have "\<forall>t. t |\<notin>| forest \<or> height t \<le> n"
    by (metis assms)
  then have "aas n (\<Psi>\<^sub>\<phi> forest) \<notin> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> forest)) \<or> length (aas n (\<Psi>\<^sub>\<phi> forest)) \<le> n"
    by (metis (full_types) finiteMaxExists(1) heightOnlyDependsOnPaths notin_fset order_trans pathsTreeForest psiPreservesPaths rev_fimage_eqI)
  then show "height t \<le> n"
    using f3 f2 by (meson lengthHeightForests)
qed 
    
    
lemma pullThroughOplus :
  assumes "\<And>lang . lang \<in> fset S \<Longrightarrow> (pathsPerLanguage lang) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))"
  shows " UNION (fset S) pathsPerLanguage \<in> fset ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S) "
proof -
  from assms(1) have a1 : "\<And> lang . lang \<in> fset S \<Longrightarrow> (\<exists> originalForest . pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> originalForest)) \<and> originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang)"
  proof -
    fix lang
    assume "lang \<in> fset S"
    hence "(pathsPerLanguage lang) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))" using assms(1) by auto
    then obtain originalPsi where "(pathsPerLanguage lang) = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  originalPsi)" and n865654 : "originalPsi \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)" by auto
    hence "originalPsi \<in> \<Psi>\<^sub>\<phi> ` lang" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
    then obtain originalForest where n8u6465 : "originalPsi = \<Psi>\<^sub>\<phi> originalForest" and n76464 : "originalForest \<in> lang" by auto
    from  n865654 \<Z>\<^sub>\<phi>\<^sub>F_def have "\<And> tree . tree |\<in>| originalPsi \<Longrightarrow> height tree \<le> n" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
    hence   "\<And>path . path |\<in>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> originalPsi)) \<Longrightarrow> length path \<le> n" using lengthInRestriction heightOnlyDependsOnPaths  finiteMaxExists  pathsTreeForest    by (metis dual_order.trans fimage_eqI)
    hence   "\<And>path . path |\<in>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> originalForest)) \<Longrightarrow> length path \<le> n" using psiPreservesPaths n8u6465 by auto
    hence "\<And>tree. tree \<in> fset originalForest \<Longrightarrow> height tree \<le> n" using lengthHeightForests notin_fset by metis
    hence "originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang" using n76464 \<Z>\<^sub>\<phi>\<^sub>F_def              using notin_fset by fastforce
    have "pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> originalForest)) \<and> originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang"
      by (simp add: \<open>originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang\<close> \<open>pathsPerLanguage lang = fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> originalPsi)\<close> n8u6465) 
    then show "(\<exists> originalForest . pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> originalForest)) \<and> originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang)"
      by auto
  qed
  def isGood == "\<lambda>  lang originalForest .(lang \<in> fset S \<longrightarrow>  (pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> originalForest)) \<and> originalForest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang))"
  from a1 isGood_def have "\<And>lang . \<exists> for . isGood lang for" by auto
  then obtain originalForests where "\<And>lang . isGood lang (originalForests lang)" using dependentChoice by auto
  hence n6565 :  "\<And>lang . (lang \<in> fset S \<Longrightarrow>  (pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> (originalForests lang))) \<and> (originalForests lang) \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang))" using isGood_def by auto
  hence n765465 : "\<And>lang . (lang \<in> fset S \<Longrightarrow>  ((originalForests lang) \<in> lang))" using \<Z>\<^sub>\<phi>\<^sub>F_def by blast
  have n8764654 : "\<Union>| (originalForests |`| S) \<in> \<Oplus> S"
  proof (simp add : bigoplusForests_def biguplusForests_def)
    from n765465 have n76554 : "\<And> lang. lang |\<in>| S \<Longrightarrow> ((originalForests lang) \<in> lang \<and> (originalForests lang) |\<subseteq>| \<Union>| (originalForests |`| S))"   by (meson ffUnion_upper fimage_eqI notin_fset) 
    have "(\<And>tr. fBex S (\<lambda>x. tr |\<in>| originalForests x) \<Longrightarrow> (\<exists>lang. lang |\<in>| S \<and> ( tr |\<in>| (originalForests lang) \<and> (originalForests lang) |\<subseteq>| \<Union>| (originalForests |`| S) \<and> (originalForests lang) \<in> lang)))"
    proof -
      fix tr
      assume "fBex S (\<lambda>x. tr |\<in>| originalForests x)"
      then obtain lang where "lang |\<in>| S" and "tr |\<in>| originalForests lang" by auto
      then have "lang |\<in>| S \<and> ( tr |\<in>| (originalForests lang) \<and> (originalForests lang) |\<subseteq>| \<Union>| (originalForests |`| S) \<and> (originalForests lang) \<in> lang)"            by (simp add: n76554) 
      then show "(\<exists>lang. lang |\<in>| S \<and> ( tr |\<in>| (originalForests lang) \<and> (originalForests lang) |\<subseteq>| \<Union>| (originalForests |`| S) \<and> (originalForests lang) \<in> lang))" by auto
    qed
    then have "(\<And>tr. fBex S (\<lambda>x. tr |\<in>| originalForests x) \<Longrightarrow> (\<exists>lang. lang |\<in>| S \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| \<Union>| (originalForests |`| S) \<and> subforest \<in> lang)))" by auto
    then show "(\<forall>tr. fBex S (\<lambda>x. tr |\<in>| originalForests x) \<longrightarrow> (\<exists>lang. lang |\<in>| S \<and> (\<exists>subforest. tr |\<in>| subforest \<and> subforest |\<subseteq>| \<Union>| (originalForests |`| S) \<and> subforest \<in> lang))) \<and>
    (\<forall>lang. lang |\<in>| S \<longrightarrow> (\<exists>subforest. subforest \<in> lang \<and> subforest |\<subseteq>| \<Union>| (originalForests |`| S)))" using n76554 by auto
  qed
  from n6565 have  "\<And>lang . (lang \<in> fset S \<Longrightarrow>  (pathsPerLanguage lang = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>   (\<Psi>\<^sub>\<phi> (originalForests lang)))))" by auto
  hence n8765654 : "\<And>lang . (lang \<in> fset S \<Longrightarrow>  (pathsPerLanguage lang = (fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi> \<circ> originalForests) lang))" by auto
  have n7u64654 : "\<And>U. fset (\<Union>| U) = \<Union> (fset ` (fset U))" using ffUnionLemma  by (simp add: ffUnion.rep_eq) 
  have n7u64654b : "\<And>U. fset (\<Union>| U) = \<Union> (fset  (fset |`| U))" using ffUnionLemma  by (simp add: ffUnion.rep_eq) 
  have "UNION (fset S) pathsPerLanguage = fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S))))"
  proof (simp add : psiPiAdditionArbitrary)
    show "(\<Union>x\<in>fset S. pathsPerLanguage x) = fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Union>| ((\<Psi>\<^sub>\<phi> \<circ> originalForests) |`| S)))"
    proof (simp add : pathsUnionCommute)
      from n7u64654 have "fset (\<Union>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> (\<Psi>\<^sub>\<phi> \<circ> originalForests)) |`| S)) = \<Union> (fset ` (fset ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> (\<Psi>\<^sub>\<phi> \<circ> originalForests)) |`| S)))" by (simp add : n7u64654)
      also have "... =  \<Union> (fset (fset |`| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> (\<Psi>\<^sub>\<phi> \<circ> originalForests)) |`| S)))" by auto
      also have "... =  \<Union> (fset ( ((fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> (\<Psi>\<^sub>\<phi> \<circ> originalForests)) |`| S)))" by auto
      also have "... =  \<Union> (fset (pathsPerLanguage |`| S))" using n8765654 by auto
      also have "... =  \<Union> ((pathsPerLanguage ` (fset S)))" by auto
      also have "... =  (\<Union>x\<in>fset S. pathsPerLanguage x)" by auto
      from calculation show "(\<Union>x\<in>fset S. pathsPerLanguage x) = fset (\<Union>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<circ> (\<Psi>\<^sub>\<phi> \<circ> originalForests)) |`| S))" by auto
    qed
  qed
  have "\<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S)) \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S)"
  proof (simp add : \<Z>\<^sub>\<phi>\<^sub>F_def)
    show "\<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S)) \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> S \<and> (\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S)) \<longrightarrow> height t \<le> n)"
    proof 
      from n8764654 show "\<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S)) \<in> \<Psi>\<^sub>\<phi> ` \<Oplus> S" by auto
      from n6565 have  "\<And>lang . (lang \<in> fset S \<Longrightarrow> (originalForests lang) \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang)" by auto
      then have "\<And>lang . (lang \<in> fset S \<Longrightarrow> (\<And> t. t |\<in>| (originalForests lang) \<Longrightarrow> height t \<le> n))" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
      then have "\<And>t. (t |\<in>| (\<Union>| (originalForests |`| S))) \<Longrightarrow> height t \<le> n" using ffUnionLemma            using notin_fset by fastforce 
      then have "\<And>t. (t |\<in>| \<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S))) \<Longrightarrow> height t \<le> n" using psiBoundedPreserved2    by blast
      then show "\<forall>t. t |\<in>| \<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S)) \<longrightarrow> height t \<le> n" by auto
    qed
  qed
  then show "UNION (fset S) pathsPerLanguage \<in> fset ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S)"
    by (simp add: \<open>UNION (fset S) pathsPerLanguage = fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<Union>| (originalForests |`| S))))\<close>) 
qed
  
    
    
  
lemma pathsArbitraryUnionLemma : "\<And> k .\<Pi>\<^sub>\<phi> (k) = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `(k)) fset" 
proof -
  fix k
  have "\<And>x . (x \<in> \<Pi>\<^sub>\<phi> (k)) = (x \<in> UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `(k)) fset)" 
  proof
    show "\<And>x. x \<in> \<Pi>\<^sub>\<phi> k \<Longrightarrow> x \<in> UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` k) fset"
    proof (simp add : pathsForForestLanguage_def)
      show "\<And>x. \<exists>t\<in>k. x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t \<Longrightarrow> \<exists>xa\<in>k. x \<in> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> xa)" using notin_fset by metis
    qed
    show "\<And>x. x \<in> UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` k) fset \<Longrightarrow> x \<in> \<Pi>\<^sub>\<phi> k"
    proof (simp add : pathsForForestLanguage_def)
      show "\<And>x. \<exists>xa\<in>k. x \<in> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> xa) \<Longrightarrow> \<exists>t\<in>k. x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t"       by (meson notin_fset) 
    qed
  qed
  then show " \<Pi>\<^sub>\<phi> k = UNION (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` k) fset" by auto
qed
  
  
  
(*lemma
  shows "closedUnderArbitraryPlus lang \<Longrightarrow> closedUnderArbitraryPlus  (((\<Psi>\<^sub>\<phi> ` lang)))"
proof (simp  add : closedUnderArbitraryPlus_def)
  assume n745646 : "\<forall>a. a \<noteq> {||} \<longrightarrow> fset a \<subseteq> lang \<longrightarrow> \<Union>| a \<in> lang "
    
  show "\<forall>a. a \<noteq> {||} \<longrightarrow> fset a \<subseteq> \<Psi>\<^sub>\<phi> ` lang \<longrightarrow> \<Union>| a \<in> \<Psi>\<^sub>\<phi> ` lang" 
  proof 
    fix a
    show "a \<noteq> {||} \<longrightarrow> fset a \<subseteq> \<Psi>\<^sub>\<phi> ` lang \<longrightarrow> \<Union>| a \<in> \<Psi>\<^sub>\<phi> ` lang"
    proof -
      assume n865654 : "a \<noteq> {||}"
      assume "fset a \<subseteq> \<Psi>\<^sub>\<phi> ` lang"
      then obtain b where n7546 : "b \<subseteq> lang" and n7465 : "fset a =  (\<Psi>\<^sub>\<phi> ` b)"          by (meson subset_imageE) 
      have "finite (fset a)" by auto
      then obtain c where "finite c" and n764564 : "fset a = (\<Psi>\<^sub>\<phi> ` c)" and n546 : "c  \<subseteq> b" using n7465     \<open>fset a = \<Psi>\<^sub>\<phi> ` b\<close> finite_subset_image
        by (metis subset_refl) 
          
      then have n764654 : "fset (Abs_fset c) = c"        by (simp add: Abs_fset_inverse) 
          
      from n865654  n764564   have "c \<noteq> {}"
        by (metis bot_fset.abs_eq fset_inverse image_empty) 
          hence n6578 : "Abs_fset c \<noteq> fempty" using n764654
            by auto 
              
          from n7546 n546 n764654 have n65 : "c \<subseteq> lang" by auto
          from n745646  n6578 n65 n764654 have "\<Union>| (Abs_fset c) \<in> lang"                by simp *)
          
              
              
lemma unionPathsArbitraryNotFinite : "\<And>(a :: abc tree set set) . \<Pi>\<^sub>\<tau> (\<Union> (a)) = (\<Union> (\<Pi>\<^sub>\<tau>` (a)))"
proof (simp add :  pathsForTreeLanguage_def )
  fix a :: "abc tree set set"
  show " {p. \<exists>y\<in>a. \<exists>t\<in>y. p |\<in>| \<Pi> t} = (\<Union>x\<in>a. {p. \<exists>t\<in>x. p |\<in>| \<Pi> t})" 
  proof
    show "{p. \<exists>y\<in>a. \<exists>t\<in>y. p |\<in>| \<delta>\<^sub>\<tau> t} \<subseteq> (\<Union>x\<in>a. {p. \<exists>t\<in>x. p |\<in>| \<delta>\<^sub>\<tau> t})" by auto
    show "(\<Union>x\<in>a. {p. \<exists>t\<in>x. p |\<in>| \<delta>\<^sub>\<tau> t}) \<subseteq> {p. \<exists>y\<in>a. \<exists>t\<in>y. p |\<in>| \<delta>\<^sub>\<tau> t}" by auto
  qed
qed
  
        
lemma pathsFsetCommute : "\<Pi>\<^sub>\<tau> \<circ> fset   = fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>" 
proof 
  have "\<And>x. (\<Pi>\<^sub>\<tau> ( fset x) = (fset ( \<Pi>\<^sub>\<iota>\<^sub>\<phi> x)))"
  proof (simp add : pathsForTreeLanguage_def pathsInForest_def)
    fix x
    show "{p. \<exists>t\<in>fset x. p |\<in>| \<Pi> t} = fset (\<Union>| (\<Pi> |`| x))"
    proof
      show "{p. \<exists>t\<in>fset x. p |\<in>| \<Pi> t} \<subseteq> fset (\<Union>| (\<Pi> |`| x))" using notin_fset ffUnionLemma        by (smt fBex.rep_eq fimage_iff mem_Collect_eq subsetI) 
          show "fset (\<Union>| (\<Pi> |`| x)) \<subseteq> {p. \<exists>t\<in>fset x. p |\<in>| \<Pi> t} "     using BasicLemmas.ffUnionLemma fBexE fimage_iff mem_Collect_eq notin_fset subsetI
          proof -
            obtain ccs :: "'c list set \<Rightarrow> 'c list set \<Rightarrow> 'c list" where
              f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (ccs x0 x1 \<in> x1 \<and> ccs x0 x1 \<notin> x0)"
              by moura
            obtain tt :: "('c tree \<Rightarrow> bool) \<Rightarrow> 'c tree fset \<Rightarrow> 'c tree" where
                  f2: "\<forall>x0 x1. (\<exists>v2. v2 |\<in>| x1 \<and> x0 v2) = (tt x0 x1 |\<in>| x1 \<and> x0 (tt x0 x1))"
              by moura
            obtain ff :: "'c list fset fset \<Rightarrow> 'c list \<Rightarrow> 'c list fset" where
              f3: "(ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<notin>| \<Union>| (\<Pi> |`| x) \<or> ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) |\<in>| \<Pi> |`| x \<and> ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<in>| ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))))) \<and> (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<in>| \<Union>| (\<Pi> |`| x) \<or> (\<forall>f. f |\<notin>| \<Pi> |`| x \<or> ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<notin>| f))"
              by (meson BasicLemmas.ffUnionLemma)
            moreover
            { assume "ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<in>| \<Pi> (tt (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t) x)"
              moreover
              { assume "\<exists>t. t \<in> fset x \<and> ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<in>| \<Pi> t"
                then have "ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) \<notin> fset (\<Union>| (\<Pi> |`| x)) \<or> ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) \<in> {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t}"
                  by blast
                then have "fset (\<Union>| (\<Pi> |`| x)) \<subseteq> {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t}"
                  using f1 by (meson subsetI) }
              ultimately have "(tt (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t) x |\<notin>| x \<or> ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) \<noteq> \<Pi> (tt (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t) x)) \<or> fset (\<Union>| (\<Pi> |`| x)) \<subseteq> {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t}"
                by (meson notin_fset) }
            moreover
            { assume "tt (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t) x |\<notin>| x \<or> ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) \<noteq> \<Pi> (tt (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t) x)"
              then have "\<not> fBex x (\<lambda>t. ff (\<Pi> |`| x) (ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x)))) = \<Pi> t)"
                using f2 by (meson fBexE)
              then have "ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<notin>| \<Union>| (\<Pi> |`| x)"
                using f3 by blast }
            ultimately have "ccs {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t} (fset (\<Union>| (\<Pi> |`| x))) |\<in>| \<Union>| (\<Pi> |`| x) \<longrightarrow> fset (\<Union>| (\<Pi> |`| x)) \<subseteq> {cs. \<exists>t. t \<in> fset x \<and> cs |\<in>| \<Pi> t}"
              by blast
            then show ?thesis
              using f1 by (meson notin_fset subsetI)
          qed  
        qed
      qed
  then show "\<And>x. (\<Pi>\<^sub>\<tau> \<circ> fset) x = (fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>) x" by auto
qed
  
    
  
lemma realizationLemma :
  fixes S1
  fixes S2
  fixes n
  fixes \<ff>
  assumes "\<And> l . l |\<in>| S1 \<Longrightarrow> closedUnderArbitraryPlus (l)"
  assumes "\<And> l . l|\<in>| S2 \<Longrightarrow> closedUnderArbitraryPlus (l)"
  assumes "\<And>l . l |\<in>| S1 \<Longrightarrow> l \<noteq> {}"
  assumes "\<And>l . l |\<in>| S2 \<Longrightarrow> l \<noteq> {}"
  defines "\<ff> == \<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (S2))))))"
  assumes "\<And> l. (l |\<in>| (S1) \<Longrightarrow> realizedInForest l \<ff>)"
  assumes "\<And> l. (l |\<in>| (S2) \<Longrightarrow> realizedInForest l \<ff>)"
    
  assumes "\<And>l forest .  l |\<in>| S1 \<Longrightarrow> forest \<in> l \<Longrightarrow> forest \<noteq> fempty"
  assumes "\<And>l forest .  l |\<in>| S2 \<Longrightarrow> forest \<in> l \<Longrightarrow> forest \<noteq> fempty"
    
  shows "\<ff> = \<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> `(\<Oplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Oplus> (S2))))))"
proof 
  from assms(5) have "\<And> path . path \<in> \<ff> \<Longrightarrow> length path \<le> n" using lengthInRestriction by auto
  show "\<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S1 \<inter> \<Psi>\<^sub>\<phi> ` \<Oplus> S2)) \<subseteq> \<ff>" using \<Z>\<^sub>\<phi>\<^sub>F_mono dual_order.trans image_mono inf_le1 inf_le2 le_infI local.\<ff>_def pathsForestLangMonotone uplusInOplus inf_mono by smt
  show "\<ff> \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S1 \<inter> \<Psi>\<^sub>\<phi> ` \<Oplus> S2)) "
  proof  -
    def pathsPerLanguage == "\<lambda> lang . (\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))})"
    from assms(6)   realizedInForest_def notin_fset  have a5 : "\<And>lang . lang \<in> fset S1 \<Longrightarrow> (\<exists>\<gg>. \<gg> \<in> lang \<and> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>) \<subseteq> \<ff>)"        by metis 
    from assms(7)   realizedInForest_def notin_fset have a6 : "\<And>lang . lang \<in> fset S2 \<Longrightarrow> (\<exists>\<gg>. \<gg> \<in> lang \<and> fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>) \<subseteq> \<ff>)"  by metis
    have a1 : "\<And>lang . lang \<in> fset S1 \<union> fset S2 \<Longrightarrow> (pathsPerLanguage lang \<noteq> {})"
    proof -
      fix lang
      assume n76453 : "lang \<in> fset S1 \<union> fset S2"
      from lengthInRestriction \<ff>_def have n9865653 : "\<And>path . path \<in> \<ff> \<Longrightarrow> length path \<le> n" by auto
      from a5 a6 n76453 obtain \<gg> where n864543 : "\<gg> \<in> lang" and n87576465654 : "fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>) \<subseteq> \<ff>" by blast
      hence "\<And>path . path \<in> (fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> \<gg>)) \<Longrightarrow> length path \<le> n" using n9865653               by auto 
      hence "\<And>tree . tree \<in> (fset \<gg>) \<Longrightarrow> height tree \<le> n" using lengthHeightForests by auto
      hence "\<gg> \<in>  \<Z>\<^sub>\<phi>\<^sub>F n lang"
      proof -
        have "\<forall>t. t |\<in>| \<gg> \<longrightarrow> height t \<le> n"             by (meson \<open>\<And>tree. tree \<in> fset \<gg> \<Longrightarrow> height tree \<le> n\<close> notin_fset)
        then show ?thesis             by (simp add: \<Z>\<^sub>\<phi>\<^sub>F_def n864543)
      qed 
      hence n875654 : "\<Psi>\<^sub>\<phi> \<gg> \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)" using zPsiCommute by auto
      def r == "fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi> (\<Psi>\<^sub>\<phi> (\<gg>)))"
      have n764564 : "r \<subseteq> \<ff>" using r_def n87576465654 psiPreservesPaths  by auto
      from n764564 r_def n875654 pathsPerLanguage_def have n764544 : "r \<subseteq> (pathsPerLanguage lang)" by auto
      from n864543   have "\<gg> \<in> lang" by auto
      hence  "\<gg> \<noteq> fempty" using assms(8) assms(9) n76453 notin_fset        by fastforce 
      hence "r \<noteq> {}" using r_def      using pathForestEmpty         by (metis bot_fset.rep_eq fset_inject  psiPreservesPaths) 
      then show "(pathsPerLanguage lang \<noteq> {})" using n764544 by auto
    qed
      
    have u6 : "\<And>lang . lang \<in> fset S1 \<union> fset S2 \<Longrightarrow> (pathsPerLanguage lang) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))"
    proof -
      fix lang
      assume nu76453 : "lang \<in> fset S1 \<union> fset S2"
      have p1 : "(pathsPerLanguage lang) =  (\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))})" using pathsPerLanguage_def by auto
      have p2 : "({r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))}) = ( (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))})))" by auto
      hence p3 : "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))}) = (\<Union> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))})))"  by auto
      have p4 : "(\<Union> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))}))) = ( ( (\<Pi>\<^sub>\<tau> (\<Union> (fset ` ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))}))))))" using unionPathsCommute by auto
      have n765478 : "closedUnderArbitraryPlus (lang)" using assms nu76453        by (meson Un_iff notin_fset)
      have "finite ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))" using restrictionIsFiniteForests \<Z>\<^sub>\<phi>\<^sub>F_def        by (metis (no_types, lifting) finite_Int finite_fset) 
      hence "finite (({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))" by simp
      hence n76987 : "fset (Abs_fset ((({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) = (({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))"        by (simp add: Abs_fset_inverse) 
      def forestsSetForClosure == "Abs_fset ((({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))"
      from closedUnderArbitraryPlus_def n765478 have n65y6i787 : "forestsSetForClosure \<noteq> {||} \<longrightarrow> fset forestsSetForClosure \<subseteq> lang \<longrightarrow> \<Union>| forestsSetForClosure \<in> lang" by auto
      have n6576 : "({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}) \<subseteq> (\<Z>\<^sub>\<phi>\<^sub>F n ( lang))" by auto
      hence "({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}) \<subseteq> (( lang))" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
      hence n64587 : "fset forestsSetForClosure \<subseteq> lang" using n76987 forestsSetForClosure_def by auto
      from a1 nu76453 pathsPerLanguage_def have "((\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))})) \<noteq> {}" by auto
      then obtain r where n65476 : "r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))" by auto
      then obtain preR where n54765 : "r = fset (\<Pi>\<^sub>\<iota>\<^sub>\<phi> preR)" and n78646 : "preR \<in> \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)"  by auto
      then obtain preR2 where n75y354 :  "preR2 \<in> lang" and n5476 :  "preR = \<Psi>\<^sub>\<phi> preR2" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
      have  n7656877 : "preR2 \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))" using n78646 n5476 n75y354 zPsiCommute psiBoundedPreserved restrictionIsFiniteForests notin_fset   by (metis (no_types, lifting) IntD2 IntI \<Z>\<^sub>\<phi>\<^sub>F_def) 
      from n65476 have "r \<subseteq> \<ff>" by auto
      hence n7656877b : "(fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  preR2)) \<subseteq> \<ff> " using  n5476 n54765 psiPreservesPaths by simp
      from forestsSetForClosure_def n76987 have n6587 : "fset forestsSetForClosure = ((({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))" by auto
      from n7656877 n7656877b n6587 have n9876465 : "fset forestsSetForClosure \<noteq> {}" by auto
      from n6576 \<Z>\<^sub>\<phi>\<^sub>F_def n6587 have "forestsSetForClosure |\<subseteq>| boundedForests n"   by (simp add: less_eq_fset.rep_eq restrictionIsFiniteForests) 
      hence "fset forestsSetForClosure \<subseteq> fset (boundedForests n)"        by (simp add: less_eq_fset.rep_eq) 
      hence "fset forestsSetForClosure \<subseteq> {f. \<forall>t. t |\<in>| f \<longrightarrow> height t \<le> n}" using restrictionIsFiniteForests by auto
      hence "fset ` (fset forestsSetForClosure) \<subseteq> {f. \<forall>t. t \<in> f \<longrightarrow> height t \<le> n}" using notin_fset             by (smt imageE mem_Collect_eq subsetCE subsetI) 
      hence "\<Union> (fset ` (fset forestsSetForClosure)) \<in> {f. \<forall>t. t \<in> f \<longrightarrow> height t \<le> n}" by auto
      hence "\<Union>| forestsSetForClosure \<in> {f. \<forall>t. t |\<in>| f \<longrightarrow> height t \<le> n}" using ffUnionLemma  by (simp add: BasicLemmas.ffUnionLemma ffUnion.rep_eq fmember.rep_eq) 
      hence n65365 : "\<Union>| forestsSetForClosure \<in> (fset (boundedForests n))" using restrictionIsFiniteForests by auto
      from n65y6i787 n64587 n9876465 have "\<Union>| forestsSetForClosure \<in> lang"  by auto
      hence "\<Union>| forestsSetForClosure \<in> (\<Z>\<^sub>\<phi>\<^sub>F n ( lang))"  using n65365 \<Z>\<^sub>\<phi>\<^sub>F_def restrictionIsFiniteForests by auto
      hence n76454 : "(\<Union> (fset ` ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))) \<in> (fset ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))" using n76987 forestsSetForClosure_def
      proof -
        have "fset (\<Union>| forestsSetForClosure) \<in> fset ` \<Z>\<^sub>\<phi>\<^sub>F n lang"      by (meson \<open>\<Union>| forestsSetForClosure \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang\<close> image_iff)
        then show ?thesis       by (simp add: ffUnion.rep_eq forestsSetForClosure_def n76987)
      qed
      have "( ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi>  ` lang)))) = \<Psi>\<^sub>\<phi>  `(((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))" using zPsiCommute by auto
      hence n7546 : "(fset `( ((\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi>  ` lang))))) = (fset `(\<Psi>\<^sub>\<phi>  `(((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))))" by auto    
      have "{r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))} = {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> (\<Psi>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}" using zPsiCommute by auto
      also have "... = \<Psi>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (\<Psi>\<^sub>\<phi> r))) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}" by auto
      also have "... = \<Psi>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}" using psiPreservesPaths by auto    
      hence "{r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))} = \<Psi>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}" using calculation by auto
      hence n76565 : "(\<Union> (fset ` ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)))}))) = (\<Union> (fset ` (\<Psi>\<^sub>\<phi> ` {r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  (r))) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))" by auto
      hence n764654 : "\<Pi>\<^sub>\<tau> (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) = (\<Union> (\<Pi>\<^sub>\<tau>` (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))" using  unionPathsArbitraryNotFinite by auto
      from n76454 have "(\<Union> (fset ` ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))) \<in> (fset ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))" by auto
      hence "\<Pi>\<^sub>\<tau> (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) \<in> \<Pi>\<^sub>\<tau> ` (fset ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))" by auto
      hence "\<Pi>\<^sub>\<tau> (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) \<in>  (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))"   using pathsInForest_def pathsForTreeLanguage_def using pathsTreeSetForest by fastforce 
      hence " (\<Union> (\<Pi>\<^sub>\<tau>` (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))))) \<in>  (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))" using  n764654 by auto
      hence " (\<Union> ((\<Pi>\<^sub>\<tau> \<circ> fset) ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) \<in>  (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))" by auto
      hence " (\<Union> ((fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>) ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) \<in>  (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))"  by (simp add : pathsFsetCommute)
      hence n8666798 : " (\<Union> ((fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))) \<in>  (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))"  by auto
      have n75465 : "\<And>y . (psi `  (\<Union> y)) = (\<Union> ( (\<lambda> e. psi ` e) ` y))" by auto
          
(*      from n76454 have "(\<Union> (fset ` ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))) \<in> (fset ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))" by auto
      hence "(\<Pi>\<^sub>\<tau> \<circ> (\<lambda> e. psi ` e)) (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))) \<in> (\<Pi>\<^sub>\<tau> \<circ> (\<lambda> e. psi ` e)) ` ( (fset ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))))" by auto
      hence "(\<Pi>\<^sub>\<tau> ( (\<lambda> e. psi ` e) (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))) \<in> (\<Pi>\<^sub>\<tau> ` ( (\<lambda> e. psi ` e)) ` ( (fset ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" by auto
      hence "(\<Pi>\<^sub>\<tau> ( (psi) ` (\<Union> (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))) \<in> (\<Pi>\<^sub>\<tau> ` ( (\<lambda> e. psi ` e)) ` ( (fset ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" by auto
      hence "(\<Pi>\<^sub>\<tau> (  (\<Union> ((\<lambda> e. psi ` e) ` (fset ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))))))) \<in> (\<Pi>\<^sub>\<tau> ` ( (\<lambda> e. psi ` e)) ` ( (fset ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" using n75465 by auto
      hence "(\<Pi>\<^sub>\<tau> (  (\<Union> (((\<lambda> e. psi ` e) \<circ> fset) ` ( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))) \<in> (\<Pi>\<^sub>\<tau> ` ((( (\<lambda> e. psi ` e))  \<circ> fset) ` ( ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))))" using n75465 by auto
          *)
          
      from psiPreservesPaths have n75465 :  "\<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi> = \<Pi>\<^sub>\<iota>\<^sub>\<phi>" by auto
      have n7556 : "\<And>r . ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi>) ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))) = (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> `(\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))" by auto
      have "(fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>) `( ({r . ((fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>) r) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})) = {r . r \<subseteq> \<ff> \<and> r \<in> ((fset \<circ> \<Pi>\<^sub>\<iota>\<^sub>\<phi>) ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))}" by auto
      hence "fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))}))) = {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))}" by auto
      hence " (\<Union> ((fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> `( ({r . (fset  (\<Pi>\<^sub>\<iota>\<^sub>\<phi>  r)) \<subseteq> \<ff> \<and> r \<in> ( (\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))})))))) = (\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))})" by auto
      hence "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))}) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" using n8666798 by auto
      hence "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi>) ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))}) \<in> (fset ` ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi>) ` ((((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" using n75465 by auto      
      hence "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` ((\<Pi>\<^sub>\<iota>\<^sub>\<phi>  \<circ> \<Psi>\<^sub>\<phi>) ` ((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))}) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi>  `((((\<Z>\<^sub>\<phi>\<^sub>F n ( lang))))))))" by auto    
      hence "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi> `(\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))}) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi>  `(((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" using n7556 by auto
      hence "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))}) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Psi>\<^sub>\<phi>  `(((\<Z>\<^sub>\<phi>\<^sub>F n ( lang)))))))" using zPsiCommute by auto
      hence n764654 : "(\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))}) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))" using n7546   by (simp add: \<open>\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang) = \<Psi>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n lang\<close>) 
      from p1 have "(pathsPerLanguage lang) =  (\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))})"  by auto
      then show "(pathsPerLanguage lang) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))"  using n764654 by auto
    qed
      
    have u5 : "\<And>S . (S = S1 \<or> S = S2) \<Longrightarrow> \<ff> = \<Union> (fset (pathsPerLanguage |`| S))"
    proof 
      show "\<And>S. S = S1 \<or> S = S2 \<Longrightarrow> \<ff> \<subseteq> \<Union>fset (pathsPerLanguage |`| S)" 
      proof 
        fix S
        assume n86564 : " S = S1 \<or> S = S2"
        fix x
        assume "x \<in> \<ff>"
        hence "x \<in> \<Pi>\<^sub>\<phi> ( (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (S2))))))" using assms(5) by auto
        then obtain forest where n8764543 : "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> forest" and n764543 : "forest \<in> (\<Z>\<^sub>\<phi>\<^sub>F n ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (S2)))))"  using pathsForForestLanguage_def by auto
        hence "forest \<in> ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S1))) \<inter> (\<Psi>\<^sub>\<phi> `(\<Uplus> (S2))))" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
        hence "forest \<in> ((\<Psi>\<^sub>\<phi> ` (\<Uplus> (S))))" using n86564 by auto
        then obtain oldForest where n85653 : "oldForest \<in> \<Uplus> (S)" and n875653543 : "forest = \<Psi>\<^sub>\<phi> oldForest" by blast
        from n875653543 psiPreservesPaths    have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest = \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldForest" by auto
        hence n864543 : "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> oldForest" using n8764543 by auto
        have n875653 : "oldForest \<noteq> fempty" using n8764543 n875653543 psiPreservesPaths fempty_iff                 using pathsTreeForest by auto 
        then obtain tree where nu864532 : "tree |\<in>| oldForest" and n86465 : "x |\<in>| \<Pi> tree" using n864543 pathsTreeForest by auto
        from biguplusForests_def n85653 nu864532 obtain lang subforest where n875543 : "lang |\<in>| S \<and> ( tree |\<in>| subforest \<and> subforest |\<subseteq>| oldForest \<and> subforest \<in> lang)" by blast
        from n875543  pathsTreeForest n864543 have "x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest"  using n86465 by blast 
        from n875653543  have "\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest = \<Pi>\<^sub>\<iota>\<^sub>\<phi> (oldForest)"
          by (simp add: psiPreservesPaths) 
        hence n1 : "\<Pi>\<^sub>\<tau> (fset oldForest) = \<Pi>\<^sub>\<tau> (fset forest) "
          by (simp add: piFset) 
        from n764543 have "\<And> tree . tree |\<in>| forest \<Longrightarrow> height tree \<le> n" using \<Z>\<^sub>\<phi>\<^sub>F_def by auto
        from n764543 have  "\<And>path . path |\<in>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> forest)) \<Longrightarrow> length path \<le> n" using lengthInRestriction heightOnlyDependsOnPaths  finiteMaxExists  pathsTreeForest
          by (metis \<open>\<And>tree. tree |\<in>| forest \<Longrightarrow> height tree \<le> n\<close> dual_order.trans fimage_eqI)
        hence  "\<And>path . path |\<in>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> oldForest)) \<Longrightarrow> length path \<le> n" using n875653543 psiPreservesPaths by auto
        hence  "\<And>path . path |\<in>| ((\<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest)) \<Longrightarrow> length path \<le> n" using n875543
          by (meson fset_rev_mp pathsTreeForest) 
        hence n875653 : "\<And> tree. tree |\<in>| subforest \<Longrightarrow> height tree \<le> n" using lengthHeightForests notin_fset by metis
        have n2 : "\<Pi>\<^sub>\<tau> (fset forest) \<subseteq> \<ff>" 
        proof 
          def language == "\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Uplus> S1 \<inter> \<Psi>\<^sub>\<phi> ` \<Uplus> S2)"
          from pathsForTreeLanguage_def have n87454 : "\<Pi>\<^sub>\<tau> (fset forest) = {p. \<exists>t\<in>(fset forest). p |\<in>| \<Pi> t} " by auto
          from pathsForForestLanguage_def \<ff>_def  language_def   have "\<ff> = {p. \<exists>t\<in>language. p |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> t}" by auto
          hence "\<ff> = {p. \<exists>t\<in>language. \<exists> tree \<in> (fset t) . p |\<in>| \<Pi> tree}" using pathsInForest_def notin_fset ffUnionLemma    by (smt Collect_cong pathsTreeForest) 
          then  show "\<And> x. x \<in> \<Pi>\<^sub>\<tau> (fset forest) \<Longrightarrow> x \<in> \<ff>" using n764543 language_def n87454 by auto
        qed
        def r == "\<Pi>\<^sub>\<tau> (fset subforest)"
        from n875543 have "subforest |\<subseteq>| oldForest" by auto
        hence "\<Pi>\<^sub>\<tau> (fset subforest) \<subseteq> \<Pi>\<^sub>\<tau> (fset oldForest)"                 by (simp add: less_eq_fset.rep_eq pathsTreeLangMonotone) 
        hence "r \<subseteq>  \<ff>" using r_def n1 n2 by auto
        from n875543  have "subforest \<in> lang" by auto
        hence "subforest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang" using n875653 \<Z>\<^sub>\<phi>\<^sub>F_def by auto
        have n864543 : "\<Pi>\<^sub>\<tau> (fset subforest) = \<Pi>\<^sub>\<tau> (fset (\<Psi>\<^sub>\<phi> subforest))"                 by (simp add: piFset psiPreservesPaths) 
        have n7644324569 : "(\<Psi>\<^sub>\<phi> subforest) \<in> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))"                      using \<open>subforest \<in> \<Z>\<^sub>\<phi>\<^sub>F n lang\<close> zPsiCommute by fastforce 
        from r_def n864543 n7644324569 have "r \<in> \<Pi>\<^sub>\<tau>\<^sub>F ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang) " by auto
        hence  "r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))" using pathsInForest_def pathsForTreeLanguage_def ffUnionLemma notin_fset          using piFset by fastforce 
        have n754654 : "x \<in> r" by (metis \<open>x |\<in>| \<Pi>\<^sub>\<iota>\<^sub>\<phi> subforest\<close> notin_fset piFset r_def)
        have n754543 : "pathsPerLanguage lang = (\<Union> {r . r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))})" using pathsPerLanguage_def by auto
        have n7u53543 : "r \<subseteq> \<ff> \<and> r \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))"                by (simp add: \<open>r \<in> fset ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)\<close> \<open>r \<subseteq> \<ff>\<close>) 
        hence n76454 : "r \<subseteq> pathsPerLanguage lang"  using n754543 by auto 
        have "lang |\<in>| S"                 by (simp add: n875543) 
        then show "x \<in> \<Union>fset (pathsPerLanguage |`| S)" using n76454 n754654          by (meson Union_iff fimage_eqI notin_fset subset_iff) 
      qed
      show "\<And>S. S = S1 \<or> S = S2 \<Longrightarrow> \<Union>fset (pathsPerLanguage |`| S) \<subseteq> \<ff>" using pathsPerLanguage_def by auto
    qed
    have "\<And>S . (S = S1 \<or> S = S2) \<Longrightarrow> \<ff> \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S))))"
    proof (simp add : u5)
      fix S
      assume "S = S1 \<or> S = S2"
      hence "\<And>lang . lang \<in> fset S \<Longrightarrow> (pathsPerLanguage lang) \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang))))" using u6 by auto
      show " UNION (fset S) pathsPerLanguage \<in> fset ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S) " using pullThroughOplus
        by (simp add: \<open>\<And>lang. lang \<in> fset S \<Longrightarrow> pathsPerLanguage lang \<in> fset ` \<Pi>\<^sub>\<iota>\<^sub>\<phi> ` \<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` lang)\<close>) 
    qed
    hence "\<ff> \<in> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S1)))) \<inter> (fset ` (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S2))))" by auto
    hence "\<ff> \<in> (fset ` (((\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S1)))) \<inter> ( (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S2))))))"            by (smt Int_iff fset_inject image_iff)  
    hence "\<ff> \<in> (fset ` (((\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Psi>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n)  (\<Oplus> S1))))) \<inter> ( (\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((\<Psi>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n)  (\<Oplus> S2)))))))))" using zPsiCommute by auto
    hence "\<ff> \<in> (fset ` (((\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((((\<Psi>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n)  (\<Oplus> S1))))) \<inter> ( ( ((\<Psi>\<^sub>\<phi> ` ((\<Z>\<^sub>\<phi>\<^sub>F n)  (\<Oplus> S2)))))))))))" using psiPiIntersection by auto
    hence "\<ff> \<in> (fset ` (((\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ((((\<Z>\<^sub>\<phi>\<^sub>F n) (\<Psi>\<^sub>\<phi> ` (  (\<Oplus> S1))))) \<inter> ( ( ((\<Z>\<^sub>\<phi>\<^sub>F n)(\<Psi>\<^sub>\<phi> ` (  (\<Oplus> S2)))))))))))" using zPsiCommute by auto
    hence "\<ff> \<in> (fset ` (((\<Pi>\<^sub>\<iota>\<^sub>\<phi> ` ( (\<Z>\<^sub>\<phi>\<^sub>F n) ( (( (\<Psi>\<^sub>\<phi> ` (  (\<Oplus> S1))))) \<inter> ( ( ((\<Psi>\<^sub>\<phi> ` (  (\<Oplus> S2))))))))))))" using zInter by auto
    then show "\<ff> \<subseteq> \<Pi>\<^sub>\<phi> (\<Z>\<^sub>\<phi>\<^sub>F n (\<Psi>\<^sub>\<phi> ` \<Oplus> S1 \<inter> \<Psi>\<^sub>\<phi> ` \<Oplus> S2)) " using piLangSum by auto
  qed
qed
  
  
        
    
    
  
end
  
src/Basic_Notations.vo src/Basic_Notations.glob src/Basic_Notations.v.beautified: src/Basic_Notations.v
src/Basic_Notations.vio: src/Basic_Notations.v
src/Basic_Notations_Set.vo src/Basic_Notations_Set.glob src/Basic_Notations_Set.v.beautified: src/Basic_Notations_Set.v src/Basic_Notations.vo
src/Basic_Notations_Set.vio: src/Basic_Notations_Set.v src/Basic_Notations.vio
src/Basic_Lemmas.vo src/Basic_Lemmas.glob src/Basic_Lemmas.v.beautified: src/Basic_Lemmas.v
src/Basic_Lemmas.vio: src/Basic_Lemmas.v
src/Relation_Properties.vo src/Relation_Properties.glob src/Relation_Properties.v.beautified: src/Relation_Properties.v ./Basic_Notations_Set.vo ./Basic_Lemmas.vo
src/Relation_Properties.vio: src/Relation_Properties.v ./Basic_Notations_Set.vio ./Basic_Lemmas.vio
src/Functions_Mappings.vo src/Functions_Mappings.glob src/Functions_Mappings.v.beautified: src/Functions_Mappings.v ./Basic_Notations_Set.vo ./Basic_Lemmas.vo ./Relation_Properties.vo
src/Functions_Mappings.vio: src/Functions_Mappings.v ./Basic_Notations_Set.vio ./Basic_Lemmas.vio ./Relation_Properties.vio
src/Tactics.vo src/Tactics.glob src/Tactics.v.beautified: src/Tactics.v
src/Tactics.vio: src/Tactics.v
src/Dedekind.vo src/Dedekind.glob src/Dedekind.v.beautified: src/Dedekind.v
src/Dedekind.vio: src/Dedekind.v
src/Conjugate.vo src/Conjugate.glob src/Conjugate.v.beautified: src/Conjugate.v
src/Conjugate.vio: src/Conjugate.v
src/Domain.vo src/Domain.glob src/Domain.v.beautified: src/Domain.v
src/Domain.vio: src/Domain.v
src/Residual.vo src/Residual.glob src/Residual.v.beautified: src/Residual.v
src/Residual.vio: src/Residual.v
src/Schroder.vo src/Schroder.glob src/Schroder.v.beautified: src/Schroder.v ./Basic_Notations_Set.vo ./Basic_Lemmas.vo ./Relation_Properties.vo ./Functions_Mappings.vo ./Dedekind.vo ./Residual.vo
src/Schroder.vio: src/Schroder.v ./Basic_Notations_Set.vio ./Basic_Lemmas.vio ./Relation_Properties.vio ./Functions_Mappings.vio ./Dedekind.vio ./Residual.vio
src/Sum_Product.vo src/Sum_Product.glob src/Sum_Product.v.beautified: src/Sum_Product.v ./Basic_Notations_Set.vo ./Basic_Lemmas.vo ./Relation_Properties.vo ./Functions_Mappings.vo ./Dedekind.vo ./Conjugate.vo ./Domain.vo
src/Sum_Product.vio: src/Sum_Product.v ./Basic_Notations_Set.vio ./Basic_Lemmas.vio ./Relation_Properties.vio ./Functions_Mappings.vio ./Dedekind.vio ./Conjugate.vio ./Domain.vio
src/Point_Axiom.vo src/Point_Axiom.glob src/Point_Axiom.v.beautified: src/Point_Axiom.v ./Basic_Notations_Set.vo ./Basic_Lemmas.vo ./Relation_Properties.vo ./Functions_Mappings.vo ./Dedekind.vo
src/Point_Axiom.vio: src/Point_Axiom.v ./Basic_Notations_Set.vio ./Basic_Lemmas.vio ./Relation_Properties.vio ./Functions_Mappings.vio ./Dedekind.vio

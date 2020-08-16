all:					std.agdai \
						induction.agdai \
						relations.agdai \
						bin.agdai \
						equality.agdai \
						isomorphism.agdai \
						connectives.agdai \
						negation.agdai \
						quantifiers.agdai \
						decidable.agdai \
						lists.agdai \
						lambda.agdai


std.agdai:				std.agda
	agda -v0 std.agda


induction.agdai: 		induction.agda
	agda -v0 induction.agda


relations.agdai:		relations.agda
	agda -v0 relations.agda


bin.agdai:				bin.agda \
						induction.agdai \
						relations.agdai
	agda -v0 bin.agda


equality.agdai:			equality.agda
	agda -v0 equality.agda	


isomorphism.agdai:		isomorphism.agda \
						bin.agdai
	agda -v0 isomorphism.agda


connectives.agdai:		connectives.agda \
						isomorphism.agdai	
	agda -v0 connectives.agda


negation.agdai:			negation.agda \
						isomorphism.agdai	
	agda -v0 negation.agda


quantifiers.agdai:		quantifiers.agda \
						isomorphism.agdai \
						bin.agdai
	agda -v0 quantifiers.agda


decidable.agdai:		decidable.agda \
						isomorphism.agdai \
						relations.agdai
	agda -v0 decidable.agda

lists.agdai:			lists.agda \
						isomorphism.agdai \
						relations.agdai \
						bin.agdai
	agda -v0 lists.agda
						

lambda.agdai:			lambda.agda \
						isomorphism.agdai \
						decidable.agdai
	agda -v0 lambda.agda
	

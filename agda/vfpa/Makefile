all:	void.agdai \
		level.agdai \
		maybe.agdai \
		func.agdai \
		prod.agdai \
   		id.agdai \
		nat.agdai \
		plus.agdai \
		mult.agdai \
		sum.agdai \
		le.agdai \
		lt.agdai \
		bool.agdai


void.agdai : 	void.agda
	agda void.agda

level.agdai : 	level.agda
	agda level.agda

maybe.agdai : 	maybe.agda
	agda maybe.agda

func.agdai : 	func.agda
	agda func.agda

prod.agdai :	prod.agda
	agda prod.agda

id.agdai : 		id.agda \
				void.agdai
	agda id.agda

nat.agdai :		nat.agda \
				id.agdai \
				void.agdai 
	agda nat.agda

plus.agdai :	plus.agda \
				id.agdai \
				nat.agdai
	agda plus.agda

mult.agdai :	mult.agda \
				id.agdai \
				nat.agdai \
				plus.agdai
	agda mult.agda

sum.agdai : 	sum.agda \
   				id.agdai \
				void.agdai	
	agda sum.agda

le.agdai :		le.agda \
				id.agdai \
				nat.agdai \
				sum.agdai \
				void.agdai
	agda le.agda

lt.agdai :		lt.agda \
				le.agdai \
				nat.agdai \
				void.agdai
	agda lt.agda

bool.agdai :	bool.agda \
			 	id.agdai \
				sum.agdai \
				void.agdai	
	agda bool.agda

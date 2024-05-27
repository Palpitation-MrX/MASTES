(* ::Package:: *)

(*
2013.09.13, nlpIpmSolver written by Qiu
2017.06.03, Refactored by Wu
2018.08.18, Dispatched by Wu
*)


BeginPackage["NumericalSolver`"]

(* Basic Functions *)
	sparseSym2Num::usage="sparseSym2Num[sym_,rule_]"
	rec2pol::usage="rec2pol[im_,re_]"
	rec2pol::usage="rec2pol[riff_]"
	pol2rec::usage="pol2rec[arg_,abs_]"
	pol2rec::usage="pol2rec[riff_]"

(* Solvers *)
	aeNewtonSolver::usage="aeNewtonSolver[equ_,varsInitRule_,para_:{5,50,10^-8,10^6,False}]\n\tSolve f(x)=0 by Newton Method."
	daeTrapezoidSolve::usage="daeTrapezoidSolve[equ_,varsInitRule_,timeRange_,para_:{5,50,10^-8,10^6}]\n\tSolve {dx/dt=f(x,y), 0=g(x,y)} by Implicit Trapezoidal Integration Method."
	nlpIpmSolver::usage="nlpIpmSolver[fFunc_,hFunc_,gFunc_,gLower_,gUpper_,vars_,varsInitRule_,para_:{5,100,10^-8,10^6,10^10,0.995,1.0,0.1,False}]\n\tSolve { Min fFunc | hFunc=0, gLower<=gFunc<=gUpper } by PCPDIPM or PDIPM."
	nlpPdIpmSolver::usage="nlpPdIpmSolver[fFunc_,hFunc_,gFunc_,gLower_,gUpper_,vars_,varsInitRule_,para_:{5,100,10^-8,10^6,10^10,0.995,1.0,0.1,False}]\n\tSolve { Min fFunc | hFunc=0, gLower<=gFunc<=gUpper } by PDIPM."


Begin["`Private`"]

sparseSym2Num[sym_,rule_]:=SparseArray[Most[ArrayRules[sym]]/.rule]

rec2pol[im_,re_]:=Flatten[{Arg[#],Abs[#]}&/@(re+I im)]

rec2pol[riff_]:=Flatten[{Arg[#],Abs[#]}&/@(riff[[2;;;;2]]+I riff[[1;;;;2]])]

pol2rec[arg_,abs_]:=Flatten[Transpose[{abs Sin[arg],abs Cos[arg]}]]

pol2rec[riff_]:=Flatten[{#[[2]]Sin[#[[1]]],#[[2]]Cos[#[[1]]]}&/@Partition[riff,2]]


(************************************************************************************************)

aeNewtonSolver[equ_,varsInitRule_,para_:{5,50,10^-8,10^6,False}]:=Module[{info,maxIter,errTol,errMax,optStep,timeBegin,hStep,varsRule,jac,itr,rhs,err,direction,res},
	{info,maxIter,errTol,errMax,optStep}=para;(* UDF FindRoot[] *)
	If[info>3,timeBegin=TimeUsed[];];
	hStep=1;
	varsRule=varsInitRule;
	varsRule[[All,2]]=varsRule[[All,2]]//N;
	If[Length[equ]!=Length[varsRule]||!NumberQ[Total[equ/.varsRule]//N],Input["aeNewtonSolver[] improper inputs : ",{MatrixForm[equ],varsRule}];Return[{varsRule,0,0,0}];];
	jac=D[equ,{varsRule[[All,1]]}]//SparseArray;

	For[itr=1,itr<=maxIter,itr++,
		rhs=equ/.varsRule;
		err=Max[Abs[rhs]];
		If[info>5,Print["itr: ",itr,", err: ",err," @ ",Position[Abs[rhs],err][[1,1]],", hStep: ",hStep];];
		If[err<errTol || err>errMax,Break[];];
		direction=LinearSolve[SparseArray[Most[ArrayRules[jac]]/.varsRule],-rhs];If[Head[direction]==LinearSolve,Input["LinearSolve[] failed in aeNewtonSolver[] : ",{itr,err,hStep}];Break[];];
		If[optStep,
			res=equ.equ/.Thread[varsRule[[All,1]]->(varsRule[[All,2]]+symStep direction)];
			hStep=symStep /.Last[FindMinimum[{res,errTol<=symStep<=2},{symStep,hStep}]];
			If[info<=5 && hStep<2errTol,Print["aeNewtonSolver[] ill-conditioned optStep : ",{MatrixForm[equ],varsRule,hStep}];];
			];
		varsRule[[All,2]] += hStep direction; 
		];
	If[info>3,Print["aeNewtonSolver[] ",itr," iterations ",If[err<errTol,"convergent! ","failed! "],{err,hStep,optStep}, " Time used: ",TimeUsed[]-timeBegin,"s"];];
	{varsRule,err,itr,hStep}
	]

daeTrapezoidSolve[equ_,varsInitRule_,timeRange_,para_:{5,50,10^-8,10^6}]:=Module[{info,maxIter,errTol,errMax,timeBegin,fEqu,gEqu,dfcEquImp,dfcEquExp,dfcEqu,xyRule,timeStep,time,data,jac,itr,err,rhs},
	{info,maxIter,errTol,errMax}=para;(* something like NDSolve[] *)
	If[info>3,timeBegin=TimeUsed[];];
	{fEqu,gEqu}=equ;
	xyRule=Flatten[varsInitRule];
	xyRule[[All,2]]=xyRule[[All,2]]//N;
	If[(Length[#]&/@equ)!=(Length[#]&/@varsInitRule)||!NumberQ[Total[Flatten[equ]/.xyRule]//N],
		Input["daeTrapezoidSolve[] improper inputs : ",{MatrixForm[fEqu],MatrixForm[gEqu],xyRule,timeRange}];Return[{{timeRange[[1]],xyRule[[All,2]]}}];];
	If[Max[Abs[gEqu/.xyRule]]>errTol,
		rhs=aeNewtonSolver[gEqu/.varsInitRule[[1]],varsInitRule[[2]]];(* make gEqu exaxt *)
		xyRule[[Length[fEqu]+1;;,2]]=rhs[[1]][[All,2]]//N;
		If[info>5,Print["daeTrapezoidSolve[] y(0) changed from ",varsInitRule[[2]]," to ",rhs[[1]],", err ",rhs[[2]]," @ ",rhs[[3]]];];
		];
	timeStep=timeRange[[3]];
	data=Table[{i,xyRule[[All,2]]},{i,timeRange[[1]],timeRange[[2]],timeStep}];(* {timeStart,timeEnd,timeStep} *)
	dfcEquImp=Join[varsInitRule[[1]][[All,1]]-timeStep fEqu/2,gEqu];
	dfcEquExp=Join[varsInitRule[[1]][[All,1]]+timeStep fEqu/2,Table[0,{Length[gEqu]}]];
	jac=D[dfcEquImp,{xyRule[[All,1]]}]//SparseArray;

	For[time=2,time<=Length[data],time++,
		dfcEqu=dfcEquImp-(dfcEquExp/.xyRule);
		For[itr=1,itr<=maxIter,itr++,
			rhs=dfcEqu/.xyRule;
			err=Max[Abs[rhs]];
			If[err<errTol||err>errMax,Break[];];
			xyRule[[All,2]]-=LinearSolve[SparseArray[Most[ArrayRules[jac]]/.xyRule],rhs];
			];
		If[err>errTol && info>5,Print["daeTrapezoidSolve[] time ",data[[time,1]]," @ ",time," failed : ",{itr,err,Position[Abs[rhs],err][[1,1]]}];
			rhs=aeNewtonSolver[gEqu/.xyRule[[;;Length[fEqu]]],xyRule[[Length[fEqu]+1;;]]];(* make gEqu exaxt *)
			If[info>5,Print["\tcorrect y for current x : ",xyRule[[Length[fEqu]+1;;]]," to ",rhs[[1]],", err ",rhs[[2]]," @ ",rhs[[3]]];];
			xyRule[[Length[fEqu]+1;;,2]]=rhs[[1]][[All,2]]//N;
			];
		data[[time,2]]=xyRule[[All,2]];
		If[info>9,Print[time," @ ",data[[time,1]]," : ",xyRule];];
		];
	If[info>3,Print["daeTrapezoidSolve[] ",timeRange, " Time used: ",TimeUsed[]-timeBegin,"s"];];
	data
	]


(************************************************************************************************)

nlpIpmSolver[fFunc_,hFunc_,gFunc_,gLower_,gUpper_,vars_,varsInitRule_,para_:{5,100,10^-8,10^6,10^10,0.995,1.0,0.1,False}]:=
	Module[{info,maxIter,errTol,errMax,gapMax,stepIPM,bPcPd,paraRule,timeBegin,varsRule,hLen,gLen,xLen,hLgrng,hLgrngRule,gLowerLgrng,gUpperLgrng,gLowerSlack,gUpperSlack,gAux,gAuxRule,gap,gapCur,gapAff,solveFunc,tmp,tmp1,tmp2,
		hx,gx,fxx,hxx,gxx,lgrng2x,lgrng2z,lgrng2w,lgrng2u,lgrng2l,prmH,lgrng2prmx,jacIpm,equIpm,varsChg,hLgrngChg,gLowerSlackChg,gUpperSlackChg,gLowerLgrngChg,gUpperLgrngChg,gLowerDDChg,gUpperDDChg,pStep,dStep,itr,rhs,err,rsl},
	If[NumberQ[vars/.varsInitRule]>0,Input["Bad varsInitRule in nlpIpmSolver[]",{vars,varsInitRule}];Return[];];
	{info,maxIter,errTol,errMax,gapMax,stepIPM,bPcPd}=para[[{1,2,3,4,5,6,9}]];
	paraRule=Thread[{pIPM,\[Sigma]IPM}->para[[{7,8}]]];
	If[info>3,timeBegin=TimeUsed[];];
	If[info>5,rsl=Table[0,{maxIter}];];

	xLen=Length[vars];
	hLen=Length[hFunc];
	gLen=Length[gFunc];
	hLgrng=ToExpression["hL"<>ToString[#]]&/@Range[hLen];
	gAux=ToString[#]&/@Range[gLen];
	gLowerLgrng=ToExpression["gLL"<>#]&/@gAux;
	gUpperLgrng=ToExpression["gUL"<>#]&/@gAux;
	gLowerSlack=ToExpression["gLS"<>#]&/@gAux;
	gUpperSlack=ToExpression["gUS"<>#]&/@gAux;
	gAux=Join[gLowerLgrng,gLowerSlack,gUpperLgrng,gUpperSlack];
	gap=gUpperSlack.gUpperLgrng-gLowerSlack.gLowerLgrng;

	varsRule=varsInitRule//Normal;
	tmp=Transpose[{#,#}]&[(gUpper-gLower)/2];(tmp1=Position[gFunc,#[[1]]];If[Length[tmp1]>0,tmp1=tmp1[[1,1]];tmp[[tmp1]]={#[[2]]-gLower[[tmp1]],gUpper[[tmp1]]-#[[2]]};];)&/@varsRule;
	varsRule=varsRule//Dispatch;
	hLgrngRule=Thread[hLgrng->0.001]//Dispatch;
	gAuxRule=Thread[gAux->(Join[-pIPM/tmp[[All,1]],tmp[[All,1]],pIPM/tmp[[All,2]],tmp[[All,2]]]/.paraRule)]//Dispatch;
	gapCur=2 gLen pIPM/.paraRule;(* gap/.gAuxRule *)pStep=dStep=1;

	hx=D[hFunc,{vars}]//SparseArray;
	gx=D[gFunc,{vars}]//SparseArray;
	fxx=D[fFunc,{vars,2}]//SparseArray;
	hxx=D[hFunc,{vars,2}]//SparseArray;
	gxx=D[gFunc,{vars,2}]//SparseArray;
	(* fx=D[fFunc,{vars}];   lgrng2y=hFunc; *)
	lgrng2x=D[fFunc,{vars}]+hLgrng.hx+(gLowerLgrng+gUpperLgrng).gx;
	lgrng2z=gFunc-gLowerSlack-gLower;
	lgrng2w=gFunc+gUpperSlack-gUpper;
	lgrng2l=gLowerLgrng gLowerSlack+pIPM;
	lgrng2u=gUpperLgrng gUpperSlack-pIPM;
	prmH=fxx+hLgrng.hxx+(gLowerLgrng+gUpperLgrng).gxx+Transpose[gx].SparseArray[DiagonalMatrix[gUpperLgrng/gUpperSlack-gLowerLgrng/gLowerSlack]].gx//SparseArray;
	lgrng2prmx=D[fFunc,{vars}]+hLgrng.hx+Transpose[gx].((gUpperLgrng lgrng2w+pIPM)/gUpperSlack-(gLowerLgrng lgrng2z+pIPM)/gLowerSlack);
	jacIpm=Join[Join[prmH,Transpose[hx],2],Join[hx,Table[0,{hLen},{hLen}],2]]//SparseArray;
	equIpm=-Join[lgrng2prmx,hFunc];

	For[itr=1,itr<=maxIter,itr++,
		rhs=equIpm/.If[bPcPd,{pIPM->0},paraRule]/.varsRule/.hLgrngRule/.gAuxRule;
		err=Max[Abs[Take[rhs,-hLen]]];(* itr, fFunc, hFunc err, hFunc pos, gap, {p, \[Sigma]}, {pStep, dStep}, err of {lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u} *)
		If[info>5,tmp1=Take[rhs,-hLen];tmp2=Position[Abs[tmp1],err][[1,1]];rsl[[itr]]={itr,fFunc/.varsRule,-tmp1[[tmp2]],tmp2,gapCur,paraRule[[All,2]],{pStep,dStep}};
			If[info>7,tmp={lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u}/.paraRule/.varsRule/.hLgrngRule/.gAuxRule;AppendTo[rsl[[itr]],Max[Abs[#]]&/@tmp];];Print[rsl[[itr]]];];
		If[(err<errTol && gapCur<errTol)||err>errMax||gapCur>gapMax,Break[];];
	
		(*solveFunc=LinearSolve[SparseArray[Most[ArrayRules[jacIpm]]/.varsRule/.hLgrngRule/.gAuxRule]];	tmp=solveFunc[rhs];	may incur ill-condition warning *)
		solveFunc=SparseArray[Most[ArrayRules[jacIpm]]/.varsRule/.hLgrngRule/.gAuxRule];
		tmp=LinearSolve[solveFunc,rhs];
		varsChg=Take[tmp,xLen];
		hLgrngChg=Take[tmp,-hLen];
		gLowerSlackChg= gx.varsChg+lgrng2z/.varsRule/.gAuxRule;
		gUpperSlackChg=-gx.varsChg-lgrng2w/.varsRule/.gAuxRule;
		gLowerLgrngChg=-(gLowerLgrng gLowerSlackChg+lgrng2l)/gLowerSlack/.If[bPcPd,{pIPM->0},paraRule]/.varsRule/.gAuxRule;
		gUpperLgrngChg=-(gUpperLgrng gUpperSlackChg+lgrng2u)/gUpperSlack/.If[bPcPd,{pIPM->0},paraRule]/.varsRule/.gAuxRule;

		If[bPcPd,
			tmp1=Select[{gLowerSlack,gLowerSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
			tmp2=Select[{gUpperSlack,gUpperSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
			pStep=Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]],1];
			tmp1=Select[{gLowerLgrng,gLowerLgrngChg}//Transpose,#[[2]]>0&]/.gAuxRule;
			tmp2=Select[{gUpperLgrng,gUpperLgrngChg}//Transpose,#[[2]]<0&]/.gAuxRule;
			dStep=Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]],1];

			gapAff=(gUpperSlack+pStep gUpperSlackChg).(gUpperLgrng+dStep gUpperLgrngChg)-(gLowerSlack+pStep gLowerSlackChg).(gLowerLgrng+dStep gLowerLgrngChg)/.gAuxRule;
			paraRule[[2,2]]=(gapAff/gapCur)^3;(*If[paraRule[[1,2]]<10errTol&&paraRule[[2,2]]<0.001,paraRule[[2,2]]=0.1;];*)
			gLowerDDChg=gLowerLgrngChg gLowerSlackChg/gLowerSlack/.gAuxRule;
			gUpperDDChg=gUpperLgrngChg gUpperSlackChg/gUpperSlack/.gAuxRule;
			rhs[[Range[xLen]]]-=Transpose[gx].(pIPM(1/gUpperSlack-1/gLowerSlack)-gUpperDDChg-gLowerDDChg)/.paraRule/.varsRule/.gAuxRule;
			(*tmp=solveFunc[rhs];*)
			tmp=LinearSolve[solveFunc,rhs];
			varsChg=Take[tmp,xLen];
			hLgrngChg=Take[tmp,-hLen];
			gLowerSlackChg= gx.varsChg+lgrng2z/.varsRule/.gAuxRule;
			gUpperSlackChg=-gx.varsChg-lgrng2w/.varsRule/.gAuxRule;
			gLowerLgrngChg=-(gLowerLgrng gLowerSlackChg+lgrng2l)/gLowerSlack-gLowerDDChg/.paraRule/.varsRule/.gAuxRule;
			gUpperLgrngChg=-(gUpperLgrng gUpperSlackChg+lgrng2u)/gUpperSlack-gUpperDDChg/.paraRule/.varsRule/.gAuxRule;
			];

		tmp1=Select[{gLowerSlack,gLowerSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		tmp2=Select[{gUpperSlack,gUpperSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		pStep=Min[stepIPM Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]]],1];
		tmp1=Select[{gLowerLgrng,gLowerLgrngChg}//Transpose,#[[2]]>0&]/.gAuxRule;
		tmp2=Select[{gUpperLgrng,gUpperLgrngChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		dStep=Min[stepIPM Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]]],1];

		varsRule=Thread[vars->(pStep varsChg+vars/.varsRule)]//Dispatch;
		hLgrngRule=Thread[hLgrng->(dStep hLgrngChg+hLgrng/.hLgrngRule)]//Dispatch;
		gAuxRule=Thread[gAux->(Join[dStep gLowerLgrngChg,pStep gLowerSlackChg,dStep gUpperLgrngChg,pStep gUpperSlackChg]+gAux/.gAuxRule)]//Dispatch;
		gapCur=gap/.gAuxRule;
		paraRule[[1,2]]=(\[Sigma]IPM/.paraRule) gapCur/2/gLen;(* pIPM *)
		];
	If[info>3,Print[If[bPcPd,"PCPD","PD"]," IPM Iteration: ",itr,", obj: ",fFunc/.varsRule,", error: ",err,", gap: ",gapCur,", time used: ",TimeUsed[]-timeBegin,"s"];
		If[info>5,tmp={lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u}/.paraRule/.varsRule/.hLgrngRule/.gAuxRule;tmp1=Max[Abs[#]]&/@tmp;tmp2=Max[tmp1];Print["\t{pIPM,\[Sigma]IPM}: ",paraRule[[All,2]],", Step: ",{pStep,dStep},"\n\tKKT error: ",tmp2," ",tmp1];];];
	{fFunc/.varsRule,varsRule,hLgrng/.hLgrngRule,gAux/.gAuxRule,If[err<errTol&&gapCur<errTol,True,False],If[info>5,rsl[[1;;(If[itr>maxIter,maxIter,itr])]],{}]}
	]

nlpPdIpmSolver[fFunc_,hFunc_,gFunc_,gLower_,gUpper_,vars_,varsInitRule_,para_:{5,100,10^-8,10^6,10^10,0.995,1.0,0.1,False}]:=
	Module[{info,maxIter,errTol,errMax,gapMax,stepIPM,paraRule,timeBegin,varsRule,hLen,gLen,xLen,hLgrng,hLgrngRule,gLowerLgrng,gUpperLgrng,gLowerSlack,gUpperSlack,gAux,gAuxRule,gap,gapCur,tmp,tmp1,tmp2,
		hx,gx,fxx,hxx,gxx,lgrng2x,lgrng2z,lgrng2w,lgrng2u,lgrng2l,prmH,lgrng2prmx,jacIpm,equIpm,varsChg,hLgrngChg,gLowerSlackChg,gUpperSlackChg,gLowerLgrngChg,gUpperLgrngChg,pStep,dStep,itr,rhs,err},
	If[NumberQ[vars/.varsInitRule]>0,Input["Bad varsInitRule in nlpPdIpmSolver[]",{vars,varsInitRule}];Return[];];
	{info,maxIter,errTol,errMax,gapMax,stepIPM}=para[[;;6]];
	paraRule=Thread[{pIPM,\[Sigma]IPM}->para[[{7,8}]]];
	If[info>3,timeBegin=TimeUsed[];];

	xLen=Length[vars];
	hLen=Length[hFunc];
	gLen=Length[gFunc];
	hLgrng=ToExpression["hL"<>ToString[#]]&/@Range[hLen];
	gAux=ToString[#]&/@Range[gLen];
	gLowerLgrng=ToExpression["gLL"<>#]&/@gAux;
	gUpperLgrng=ToExpression["gUL"<>#]&/@gAux;
	gLowerSlack=ToExpression["gLS"<>#]&/@gAux;
	gUpperSlack=ToExpression["gUS"<>#]&/@gAux;
	gAux=Join[gLowerLgrng,gLowerSlack,gUpperLgrng,gUpperSlack];
	gap=gUpperSlack.gUpperLgrng-gLowerSlack.gLowerLgrng;

	varsRule=varsInitRule//Normal;
	tmp=Transpose[{#,#}]&[(gUpper-gLower)/2];(tmp1=Position[gFunc,#[[1]]];If[Length[tmp1]>0,tmp1=tmp1[[1,1]];tmp[[tmp1]]={#[[2]]-gLower[[tmp1]],gUpper[[tmp1]]-#[[2]]};];)&/@varsRule;
	varsRule=varsRule//Dispatch;
	hLgrngRule=Thread[hLgrng->0.001]//Dispatch;
	gAuxRule=Thread[gAux->(Join[-pIPM/tmp[[All,1]],tmp[[All,1]],pIPM/tmp[[All,2]],tmp[[All,2]]]/.paraRule)]//Dispatch;
	gapCur=2 gLen pIPM/.paraRule;(* gap/.gAuxRule *)pStep=dStep=1;

	hx=D[hFunc,{vars}]//SparseArray;
	gx=D[gFunc,{vars}]//SparseArray;
	fxx=D[fFunc,{vars,2}]//SparseArray;
	hxx=D[hFunc,{vars,2}]//SparseArray;
	gxx=D[gFunc,{vars,2}]//SparseArray;
	(* fx=D[fFunc,{vars}];   lgrng2y=hFunc; *)
	lgrng2x=D[fFunc,{vars}]+hLgrng.hx+(gLowerLgrng+gUpperLgrng).gx;
	lgrng2z=gFunc-gLowerSlack-gLower;
	lgrng2w=gFunc+gUpperSlack-gUpper;
	lgrng2l=gLowerLgrng gLowerSlack+pIPM;
	lgrng2u=gUpperLgrng gUpperSlack-pIPM;
	prmH=fxx+hLgrng.hxx+(gLowerLgrng+gUpperLgrng).gxx+Transpose[gx].SparseArray[DiagonalMatrix[gUpperLgrng/gUpperSlack-gLowerLgrng/gLowerSlack]].gx//SparseArray;
	lgrng2prmx=D[fFunc,{vars}]+hLgrng.hx+Transpose[gx].((gUpperLgrng lgrng2w+pIPM)/gUpperSlack-(gLowerLgrng lgrng2z+pIPM)/gLowerSlack);
	jacIpm=Join[Join[prmH,Transpose[hx],2],Join[hx,Table[0,{hLen},{hLen}],2]]//SparseArray;
	equIpm=-Join[lgrng2prmx,hFunc];

	For[itr=1,itr<=maxIter,itr++,
		rhs=equIpm/.paraRule/.varsRule/.hLgrngRule/.gAuxRule;
		err=Max[Abs[Take[rhs,-hLen]]];
		If[info>5,tmp1=Take[rhs,-hLen];tmp2=Position[Abs[tmp1],err][[1,1]];Print[{itr,fFunc/.varsRule,-tmp1[[tmp2]],tmp2,gapCur,paraRule[[All,2]],{pStep,dStep}}];
			If[info>7,tmp={lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u}/.paraRule/.varsRule/.hLgrngRule/.gAuxRule;Print["\terr KKT: ",Max[Abs[#]]&/@tmp]];];
		If[(err<errTol && gapCur<errTol)||err>errMax||gapCur>gapMax,Break[];];
	
		tmp=LinearSolve[SparseArray[Most[ArrayRules[jacIpm]]/.varsRule/.hLgrngRule/.gAuxRule],rhs];
		varsChg=Take[tmp,xLen];
		hLgrngChg=Take[tmp,-hLen];
		gLowerSlackChg= gx.varsChg+lgrng2z/.varsRule/.gAuxRule;
		gUpperSlackChg=-gx.varsChg-lgrng2w/.varsRule/.gAuxRule;
		gLowerLgrngChg=-(gLowerLgrng gLowerSlackChg+lgrng2l)/gLowerSlack/.paraRule/.varsRule/.gAuxRule;
		gUpperLgrngChg=-(gUpperLgrng gUpperSlackChg+lgrng2u)/gUpperSlack/.paraRule/.varsRule/.gAuxRule;

		tmp1=Select[{gLowerSlack,gLowerSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		tmp2=Select[{gUpperSlack,gUpperSlackChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		pStep=Min[stepIPM Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]]],1];
		tmp1=Select[{gLowerLgrng,gLowerLgrngChg}//Transpose,#[[2]]>0&]/.gAuxRule;
		tmp2=Select[{gUpperLgrng,gUpperLgrngChg}//Transpose,#[[2]]<0&]/.gAuxRule;
		dStep=Min[stepIPM Min[-tmp1[[All,1]]/tmp1[[All,2]],-tmp2[[All,1]]/tmp2[[All,2]]],1];

		varsRule=Thread[vars->(pStep varsChg+vars/.varsRule)]//Dispatch;
		hLgrngRule=Thread[hLgrng->(dStep hLgrngChg+hLgrng/.hLgrngRule)]//Dispatch;
		gAuxRule=Thread[gAux->(Join[dStep gLowerLgrngChg,pStep gLowerSlackChg,dStep gUpperLgrngChg,pStep gUpperSlackChg]+gAux/.gAuxRule)]//Dispatch;
		gapCur=gap/.gAuxRule;
		paraRule[[1,2]]=(\[Sigma]IPM/.paraRule) gapCur/2/gLen;(* pIPM *)
		];
	If[info>3,Print["nlpPdIpmSolver[] ",itr," iterations ",If[!(err<errTol && gapCur<errTol),"divergent!","convergent!"], " Time used: ",TimeUsed[]-timeBegin,"s"];
		If[info>5,tmp={lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u}/.paraRule/.varsRule/.hLgrngRule/.gAuxRule;tmp1=Max[Abs[#]]&/@tmp;tmp2=Max[tmp1];
			Print["obj: ",fFunc/.varsRule,", error: ",err,", gap: ",gapCur,", pIPM: ",pIPM/.paraRule,", \[Sigma]: ",\[Sigma]IPM/.paraRule,", Step: ",{pStep,dStep},", KKT: ",tmp2];If[info>7,Print["\terr KKT: ",tmp1];];
			(tmp=Position[Thread[(#[[1]]/.gAuxRule)<10errTol],True]//Flatten;If[Length[tmp]>0,Print["\t",Length[tmp]," "<>#[[2]]<>" limits: ",gFunc[[tmp]]];];)&/@{{gLowerSlack,"lower"},{gUpperSlack,"upper"}}];];
	{fFunc/.varsRule,varsRule,hLgrng/.hLgrngRule,gAux/.gAuxRule,If[err<errTol&&gapCur<errTol,True,False],{}}
	]

End[]

EndPackage[]

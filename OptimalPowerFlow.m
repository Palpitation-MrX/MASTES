(* ::Package:: *)

(*
2017.05.12, Refactored by Wu
2018.08.18, Dispatched by Wu
*)


BeginPackage["OptimalPowerFlow`",{"Global`","NumericalSolver`"}]
(* Package needs Global`variables NumericalSolver`nlpIpmSolver *)

formOpfModel::usage="formOpfModel[model_:``pLoss``,info_:5]\n\tOPF model should be one of loadMargin, fuelCost, pLoss(default)."

initOpfVars::usage="initOpfVars[md_:{},info_:5]\n\tOPF Vars Initial Method should be one of flat(default), Current(whatever current available)."

solveOpf::usage="solveOpf[para_:{100,10^-8,10^8,10^10,0.995,1.0,0.1,True},info_:5]"


(* Begin["`Private`"] - End[] result a too narrow context that Global`variable cannot be decleared here *)

formOpfModel[model_:"pLoss",info_:5]:=Module[{consRule},(* local variables  *)
	Global`fFunc;(* Declear Global`variable *)
	Global`hFunc;
	Global`gFunc;
	Global`gLower;
	Global`gUpper;
	Global`varsOpf;

	avBusRule0=Thread[avBusA->Riffle[busPara[[new2old,10]] Degree,ReplacePart[busPara[[new2old,9]],Thread[(pvBus~Join~avBus)->genPara[[pvGen~Join~avGen,6]]]]]];
	pqGenRule0=Thread[pqGenA->Riffle[genPara[[All,4]],genPara[[All,5]]]];
	pqLoadRule0=Thread[pqLoadA->Riffle[loadPara[[All,4]],loadPara[[All,5]]]];
	Which[
		model=="loadMargin",
			Global`loadLevel;(* Declear Global`variable *)
			varsOpf=Flatten[{avBusA[[Delete[Range[2 nBus],2avBus-1]]],pGenA[[avGen]],qGenA,loadLevel}];
			consRule=Flatten[{avBusRule0[[2avBus-1]],pqGenRule0[[2Delete[Range[nGen],avGen]-1]],pqLoadRule0}];
			fFunc=-loadLevel;
			hFunc=pfEquTot/.yRule/.consRule;
			hFunc[[2genPara[[All,1]]-1]]+=loadLevel pGenA/.consRule;
			hFunc[[2loadPara[[All,1]]-1]]-=loadLevel pLoadA/.consRule;
			hFunc[[2loadPara[[All,1]]]]-=loadLevel qLoadA/.consRule;
			gFunc={voltA,pGenA[[avGen]],qGenA}//Flatten;
			gLower={busPara[[All,12]],genPara[[avGen,11]],genPara[[All,9]]}//Flatten;
			gUpper={busPara[[All,11]],genPara[[avGen,10]],genPara[[All,8]]}//Flatten;,
		model=="fuelCost",
			varsOpf=Flatten[{avBusA[[Delete[Range[2nBus],2avBus-1]]],pqGenA}];
			consRule=Flatten[{avBusRule0[[2avBus-1]],pqLoadRule0}];
			fFunc=Total[genPara[[All,12]]+genPara[[All,13]]pGenA+genPara[[All,14]]pGenA^2];
			hFunc=pfEquTot/.yRule/.consRule;
			gFunc={voltA,pGenA,qGenA}//Flatten;
			gLower={busPara[[All,12]],genPara[[All,11]],genPara[[All,9]]}//Flatten;
			gUpper={busPara[[All,11]],genPara[[All,10]],genPara[[All,8]]}//Flatten;,
		True,If[model!="pLoss",Input["Unknown opfModel: ",model,", use default pLoss."];];
			varsOpf=Flatten[{avBusA[[Delete[Range[2nBus],2avBus-1]]],pGenA[[avGen]],qGenA}];
			consRule=Flatten[{avBusRule0[[2avBus-1]],pqGenRule0[[2Delete[Range[nGen],avGen]-1]],pqLoadRule0}];
			fFunc=Total[pGenA[[avGen]]];
			hFunc=pfEquTot/.yRule/.consRule;
			gFunc={voltA,qGenA}//Flatten;
			gLower={busPara[[All,12]],genPara[[All,9]]}//Flatten;
			gUpper={busPara[[All,11]],genPara[[All,8]]}//Flatten;			
		];
	{fFunc,hFunc,gFunc,gLower,gUpper}=Chop[{fFunc,hFunc,gFunc,gLower,gUpper}];
	If[info>1,Print["Optimal Power Flow Model: ",model,", Equality constraints (",Length[hFunc],"), Nonequality constraints (",Length[gFunc],"), ", "Variables (",Length[varsOpf],")"];
		If[info>7,Print["OPF Obj: ",fFunc];Print["Equality constraints: ",MatrixForm[hFunc]];Print["Nonequality constraints: ",MatrixForm[Thread[gLower<=gFunc<=gUpper]]];Print["Variables: ",varsOpf];];];
	]

initOpfVars[md_:{},info_:5]:=Module[{initRule,busInitRule,tmp1,tmp2},
	Global`varsOpfInitRule;(* Declear Global`variable *)
	initRule=If[Head[md]===List,md,{}];
	{pqBus,pvBus,avBus}=Flatten[Position[busPara[[new2old,4]],#]]&/@{1,2,3};
	{pqGen,pvGen,avGen}=Flatten[Position[genPara[[All,1]],#]&/@#]&/@{pqBus,pvBus,avBus};
	busInitRule=If[md=="caseData",avBusRule0,tmp1=Thread[(2 pqBus~Join~pvBus -1)->Table[0,{nBus-Length[avBus]}]];tmp2=Thread[(2 pqBus)->Table[1,{Length[pqBus]}]];
		Thread[avBusA->ReplacePart[avBusRule0[[All,2]],tmp1~Join~tmp2]]];
	varsOpfInitRule=Thread[varsOpf->(varsOpf/.initRule/.busInitRule/.pqGenRule0/.pqLoadRule0/.{loadLevel->1}//N)];

	MapIndexed[(tmp1=Position[gFunc,#1[[1]]];tmp1=If[Length[tmp1]>0,tmp1[[1,1]],0];tmp2=!NumberQ[#1[[2]]];
		If[tmp1==0,If[tmp2,varsOpfInitRule[[First[#2],2]]=0.0;];,	(*varsOpfInitRule[[First[#2],2]]=(gLower[[tmp1]]+gUpper[[tmp1]])/2.0;];)&,varsOpfInitRule];*)
			If[tmp2||#1[[2]]<gLower[[tmp1]]+100errTol||#1[[2]]>gUpper[[tmp1]]-100errTol,varsOpfInitRule[[First[#2],2]]=(gLower[[tmp1]]+gUpper[[tmp1]])/2.0;];];)&,varsOpfInitRule];
	If[info>7,Print["varsOpfInitRule (",Length[varsOpfInitRule],"): ",varsOpfInitRule];];
	]

solveOpf[para_:{100,10^-8,10^8,10^10,0.995,1.0,0.1,True},info_:5]:=Module[{rslOpf,bSolved,tmp1,tmp2,figA,figB,figC,figD},
	Global`fFuncVal;(* Declear Global`variable *)
	Global`varsOpfRule;
	Global`hLgrngVal;
	Global`gAuxVal;(* {gLowerLgrng,gLowerSlack,gUpperLgrng,gUpperSlack} *)

	If[info>1,Print["Solved by",If[para[[8]]," Predictor\[Dash]Corrector "," "],"Primal-Dual Interior Point Method ##############"];];
	{fFuncVal,varsOpfRule,hLgrngVal,gAuxVal,bSolved,rslOpf}=nlpIpmSolver[fFunc,hFunc,gFunc,gLower,gUpper,varsOpf,varsOpfInitRule,Prepend[para,info]];

	If[!bSolved,Print["IPM divergent with ",Thread[{"maxIter","errTol","errMax","gapMax","stepIPM","pIPM","\[Sigma]IPM","bPcpd"}->N[para]]];,
		If[info>1,
			avBusRule=Thread[avBusA->(avBusA/.varsOpfRule/.avBusRule0)];
			pqGenRule=Thread[pqGenA->(pqGenA/.varsOpfRule/.pqGenRule0)];
			pqLoadRule=Thread[pqLoadA->(pqLoadA/.varsOpfRule/.pqLoadRule0)];
			busInfoPrint[info];brchInfoPrint[info];
			tmp1=Length[gFunc];
			(tmp2=Position[Thread[#[[1]]<10errTol],True]//Flatten;If[Length[tmp2]>0,Print[#[[2]]," limits (",Length[tmp2],"): ",gFunc[[tmp2]]];];)&/@{{gAuxVal[[tmp1+1;;2tmp1]],"Lower"},{gAuxVal[[3tmp1+1;;]],"Upper"}};
			];];
		(* itr, fFunc, hFunc-err, hFunc-pos, gap, {p, \[Sigma]}, {pStep, dStep}, err of {lgrng2x,hFunc,lgrng2z,lgrng2w,lgrng2l,lgrng2u} *)
	If[info>7 && Length[rslOpf]>1,
		figA=ListPlot[rslOpf[[All,{1,2}]],AxesLabel->{"Itr","fFunc"},PlotStyle->Red,PlotRange->All];
		figB=ListLogPlot[rslOpf[[All,{1,5}]],AxesLabel->{"Itr","gap"},PlotStyle->Red,PlotRange->All];
		figC=ListLogPlot[Transpose[{rslOpf[[All,1]],Abs[rslOpf[[All,3]]]}],AxesLabel->{"Itr","hFunc Err"},PlotStyle->Red,PlotRange->All];
		figD=ListLogPlot[Transpose[{rslOpf[[All,1]],Max[#]&/@rslOpf[[All,8]]}],AxesLabel->{"Itr","KKT Err"},PlotStyle->Red,PlotRange->All];
		Print[GraphicsRow[{figA,figB,figC,figD},ImageSize->1200]];
		];
	]

EndPackage[]

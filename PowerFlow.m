(* ::Package:: *)

(*
2010.06.26, Created by Wu
2017.04.25, Refactored by Wu
2018.08.18, Dispatched by Wu
*)



(* Main Variables
	Parameter:	bTapChg, qLimit, pfSolMd, bPolRec
	InputData:	busPara, loadPara, genPara, linePara, kxfmPara, axfmPara, new2old
	Number:		nBus, nLoad, nGen, nLine, nKxfm, nAxfm
	StrName:	genName, loadName, busName
	Ymatrix:	yMatrix, gYsym, bYsym, yRule
	xformer:	kxfmA, axfmA, kxfmRule, axfmRule
	Voltage:	anglA, voltA, avBusA, voltReA, voltImA, avRecA, avBusRule
	BusType:	pqBus, pvBus, avBus, pvGen, avGen
	Gen:		pGenA, qGenA, pqGenA, pqGenRule
	Load:		pLoadA, qLoadA, pqLoadA, pqLoadRule
	Equation:	pfEquTot

	Dc Power Flow
		YdcMatrix:	yDcMatrix, brchDcPara, avBus, avGen
		Vector:		anglDcA, pGenDcA, pLoadDcA, anglDcRule, pGenDcRule, pLoadDcRule
		Equation:	yMat, pRgt
*)
(* Functions
	readData::usage="readData[info_:5]"
	formYMatrix::usage="formYMatrix[info_:5]"
	definePfSym::usage="definePfSym[info_:5]"
	formPfEquTot::usage="formPfEquTot[info_:5]"

	initPf::usage="initPf[md_:{},info_:5]"
	solvePf::usage="solvePf[info_:5]"

		updateQgen::usage="updateQgen[]"
		checkLimit::usage="checkLimit[iter_,info_:5]"

		formPfEquNewton::usage="formPfEquNewton[]"
		solvePflowNewton::usage="solvePflowNewton[info_:5,errTol_:10^-8,maxItr_:50,errMax_:10^8]"

		formPfEquPQ::usage="formPfEquPQ[first_:True]"
		solvePflowPQ::usage="solvePflowPQ[info_:5,errTol_:10^-8,maxItr_:100,errMax_:10^8]"

		solvePflowGS::usage="solvePflowGS[info_:5,errTol_:10^-4,maxItr_:500,errMax_:10^8]"

		formBrchFlowEqu::usage="formBrchFlowEqu[k_,brch_,shunt_:True]"
		brchInfoPrint::usage="brchInfoPrint[info_:5]"
		busInfoPrint::usage="busInfoPrint[info_:5]"

	dcPowerFlow::usage="dcPowerFlow[info_:5]"

		formYdcMatrix::usage="formYdcMatrix[info_:5]"
		definePfDcSym::usage="definePfDcSym[info_:5]"
		formPfEquDc::usage="formPfEquDc[info_:5]"

		dcPfInfoPrint::usage="dcPfInfoPrint[info_:5]"
		busRslAcDcCmp::usage="busRslAcDcCmp[]"
		brchRslAcDcCmp::usage="brchRslAcDcCmp[]"
*)

(************************************************************************************************)
(* Bus format:  num I name type Vbase area GL BL V A Vmax Vmin *)
(* Load format: num I ID PL QL IP IQ YP YQ *)
(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
(* Line format: numI numJ I J Ckt R X B Pmax Pmin *)
(* Xfrm format: numI numJ I J Ckt R X Tk Ta Ttype Tmax Tmin Tap Ireg Cmax Cmin G B Name Pmax Pmin *)
(* Brch format: numI numJ G+IB Gi+IBi Gj+IBj *)

readData[info_:5]:=Module[{},
	{busPara,loadPara,genPara,linePara,kxfmPara,axfmPara,genDyn,genAux,new2old,new2busID}=caseData[caseName,optNode,info];
	{nBus,nLoad,nGen,nLine,nKxfm,nAxfm,nGenDyn,nGenAux}=Length[#]&/@{busPara,loadPara,genPara,linePara,kxfmPara,axfmPara,genDyn,genAux};
	busName=ToString[#]&/@new2busID[[Range[nBus]]];
	genName=ToString[#]&/@genPara[[All, 2]];
	loadName=ToString[#]&/@loadPara[[All, 2]];
	Print[MatrixForm[{{"nBus","nLoad","nGen","nLine","nKxfm","nAxfm","nGenDyn","nGenAux"},{nBus,nLoad,nGen,nLine,nKxfm,nAxfm,nGenDyn,nGenAux}}]];
	If[info>9,Print["Bus:  ", MatrixForm[busPara]]; Print["Load: ", MatrixForm[loadPara]]; Print["Gen:  ", MatrixForm[genPara]];Print["Line: ", MatrixForm[linePara]]; 
		Print["Kxfm: ", MatrixForm[kxfmPara]]; Print["Axfm: ", MatrixForm[axfmPara]];Print["GenDyn: ", MatrixForm[genDyn]]; Print["GenAux: ", MatrixForm[genAux]];];
	If[Length[Position[busPara[[All,4]],3]]!=1,Print["Warning: slack bus number \[NotEqual] 1 ",Select[busPara,#[[4]]==3&]];];
	If[nAxfm!=0,Print["Warning: nAxfm\[NotEqual]0"];];
	]

formYMatrix[info_:5]:=Module[{brchPara,nBrch,aInMat,tmp,tmp1,tmp2},
	If[nKxfm!=0&&bTapChg,
		kxfmA=(ToExpression["tk"<>busName[[#[[1]]]]<>"x"<>busName[[#[[2]]]]])&/@kxfmPara;kxfmRule=Thread[kxfmA->kxfmPara[[All,8]]]//Dispatch;,
		kxfmA=kxfmPara[[All,8]];kxfmRule={};];
	If[nAxfm!=0&&bTapChg,
		axfmA=Flatten[#]&/@(ToExpression[{"xk"<>#,"xa"<>#}]&/@{busName[[#[[1]]]]<>"x"<>busName[[#[[2]]]]}&/@axfmPara);axfmRule=Thread[Flatten[axfmA]->Flatten[axfmPara[[All,{8,9}]]]]//Dispatch;,
		axfmA=axfmPara[[All,{8,9}]];axfmRule={};];
	tmp1=If[nAxfm==0,{},
		tmp=1/(axfmPara[[All,6]]+I axfmPara[[All,7]]);tmp2=(Cos[axfmA[[All,2]]]-I Sin[axfmA[[All,2]]])/axfmA[[All,1]];
		Transpose[{axfmPara[[All,1]],axfmPara[[All,2]],tmp tmp2,tmp(1/axfmA[[All,1]]^2-tmp2)+axfmPara[[All,17]]+I axfmPara[[All,18]],tmp(1-tmp2)}]];
	(*   I1 = U1/(z k^2) - U2/(z k^T)    I1 = (y10+y12) U1 - y12 U2      y12 = 1/(z k^T)        y10 = 1/(z k^2) - 1/(z k^T)
	     I2 = U1/(z k) - U2/z            I2 = y21 U1 - (y20+y21) U2      y21 = 1/(z k)          y20 = 1/z - 1/(z k)                 *)
	tmp2=If[nKxfm==0,{},
		tmp=1/(kxfmPara[[All,6]]+I kxfmPara[[All,7]]);Transpose[{kxfmPara[[All,1]],kxfmPara[[All,2]],tmp/kxfmA,tmp (1-kxfmA)/kxfmA^2+kxfmPara[[All,17]]+I kxfmPara[[All,18]],tmp (kxfmA-1)/kxfmA}]];
	brchPara=Join[If[nLine==0,{},Transpose[{linePara[[All,1]],linePara[[All,2]],1/(linePara[[All,6]]+I linePara[[All,7]]),I linePara[[All,8]],I linePara[[All,8]]}]],tmp2,tmp1];
	nBrch=nLine+nKxfm+nAxfm;
	aInMat=SparseArray[Flatten[MapIndexed[{{#1[[1]],First[#2]}->1,{#1[[2]],First[#2]}->-1}&,brchPara],1],{nBus,nBrch}];
	tmp=Table[0,{nBus}];
	(tmp[[#[[1]]]]+=#[[7]]+I #[[8]])&/@busPara;
	(tmp[[#[[1]]]]+=#[[4]];tmp[[#[[2]]]]+=#[[5]])&/@brchPara;
	yMatrix=aInMat.DiagonalMatrix[brchPara[[All,3]]].Transpose[aInMat]+DiagonalMatrix[tmp]//Chop//SparseArray;
	If[nAxfm!=0,tmp1=2 I Sin[axfmA[[All,2]]]/axfmA[[All,1]]/(axfmPara[[All,6]]+I axfmPara[[All,7]]);
		MapIndexed[(yMatrix[[#1[[1]],#1[[2]]]]-=tmp1[[First[#2]]]//Chop;)&,axfmPara];];
	If[info>7,Print["yMatrix formed."];If[info>12,Print[MatrixForm[brchPara]];Print[MatrixForm[yMatrix]];];];
	]

definePfSym[info_:5]:=Module[{tmp},
	tmp=ArrayRules[yMatrix]//Most;
	gYsym=SparseArray[(#[[1]]->ToExpression["g"<>busName[[#[[1,1]]]]<>"x"<>busName[[#[[1,2]]]]])&/@tmp,{nBus,nBus}];
	bYsym=SparseArray[(#[[1]]->ToExpression["b"<>busName[[#[[1,1]]]]<>"x"<>busName[[#[[1,2]]]]])&/@tmp,{nBus,nBus}];
	yRule=ComplexExpand[Flatten[{Extract[gYsym,#[[1]]]->Re[#[[2]]],Extract[bYsym,#[[1]]]->Im[#[[2]]]}&/@tmp]]//Dispatch;(* ComplexExpand can slow down *)
	anglA=ToExpression["a"<>#]&/@busName;
	voltA=ToExpression["v"<>#]&/@busName;
	avBusA=Riffle[anglA,voltA];
	If[bPolRec,
		voltReA=voltA Cos[anglA];
		voltImA=voltA Sin[anglA];
		avRecA=avBusA;,
		voltReA=ToExpression["ve"<>#]&/@busName;
		voltImA=ToExpression["vf"<>#]&/@busName;
		avRecA=Riffle[voltImA,voltReA];];
	pGenA=ToExpression["pG"<>#]&/@genName;
	qGenA=ToExpression["qG"<>#]&/@genName;
	pqGenA=Riffle[pGenA,qGenA];
	pqGenRule=Thread[pqGenA->Riffle[genPara[[All,4]],genPara[[All,5]]]]//Dispatch;
	If[nLoad==0,pLoadA=qLoadA=pqLoadA=pqLoadRule={};,
		pLoadA=ToExpression["pL"<>#]&/@loadName;
		qLoadA=ToExpression["qL"<>#]&/@loadName;
		pqLoadA=Riffle[pLoadA,qLoadA];
		pqLoadRule=Thread[pqLoadA->Riffle[loadPara[[All,4]],loadPara[[All,5]]]]//Dispatch;];
	If[info>7,Print["Power Flow Symbols defined."]];
	]

formPfEquTot[info_:5]:=Module[{tmp,pg,qg,pl,ql,real,imag,pEqu,qEqu},
	tmp=Table[0,{nBus}];
	{pg,qg}=ReplacePart[tmp,Thread[genPara[[All,1]]->#]]&/@{pGenA,qGenA};
	If[nLoad==0,pl=ql=tmp,{pl,ql}=ReplacePart[tmp,Thread[loadPara[[All,1]]->#]]&/@{pLoadA,qLoadA};];
	real=gYsym.voltReA-bYsym.voltImA;
	imag=gYsym.voltImA+bYsym.voltReA;
	pEqu=TrigReduce[pg-pl-(voltReA real+voltImA imag)];
	qEqu=TrigReduce[qg-ql-(voltImA real-voltReA imag)];
	pfEquTot=Riffle[pEqu,qEqu]//Chop;
	If[info>7,Print["Full power flow equation formed."]];
	]

(**************************************** Power Flow Common Function ****************************************)

initPf[md_:{},info_:5]:=Module[{aset,vset},
	{pqBus,pvBus,avBus}=Flatten[Position[busPara[[new2old,4]],#]]&/@{1,2,3};
	{pqGen,pvGen,avGen}=Flatten[Position[genPara[[All,1]],#]&/@#]&/@{pqBus,pvBus,avBus};
	If[Head[md]==List&&Length[md]==Length[avBusA],
		If[info>3,Print["Direct avBusRule power flow initialization."];];
		avBusRule=ReplacePart[md,Thread[ArrayPad[Partition[2(pvBus~Join~avBus),1],{{0},{0,1}},2]-> genPara[[pvGen~Join~avGen,6]]]]//Dispatch;Return[];];
	vset=Thread[(pvBus~Join~avBus)->genPara[[pvGen~Join~avGen,6]]];
	If[md=="caseData",
		If[info>3,Print["Direct caseData power flow initialization."];];
		avBusRule=Thread[avBusA->Riffle[busPara[[new2old,10]] Degree,ReplacePart[busPara[[new2old,9]],vset]]]//Dispatch;Return[];];
	If[md!="flat",Print["Unknown initPf method: ",md];];
	If[info>3,Print["Flat power flow initialization."];];
	aset=Thread[avBus->(busPara[[new2old[[avBus]],10]]Degree)];
	avBusRule=Thread[avBusA->Riffle[ReplacePart[Table[Mean[aset[[All,2]]],{nBus}],aset],ReplacePart[Table[1,{nBus}],vset]]]//Dispatch;
	]

updateQgen[]:=Module[{qGenPos,qBusPos,vnew},pqGenRule=pqGenRule//Normal;
	qGenPos=Join[2 avGen-1,2 avGen,2 pvGen];
	qBusPos=Join[2 avBus-1,2 avBus,2 genPara[[pvGen,1]]];
	vnew=pqGenA[[qGenPos]]-pfEquTot[[qBusPos]]/.yRule/.kxfmRule/.axfmRule/.pqLoadRule/.pqGenRule/.If[bPolRec,avBusRule,Thread[avRecA->pol2rec[avBusA/.avBusRule]]//Dispatch];
	pqGenRule[[qGenPos]]=Thread[pqGenA[[qGenPos]]->vnew];pqGenRule=pqGenRule//Dispatch;
	Position[{Thread[qGenA<=genPara[[All,8]]],Thread[genPara[[All,9]]<=qGenA]}/.pqGenRule,False]
	]

checkLimit[iter_,info_:5]:=Module[{pos,itr,num,genI,bGtMax},
	pos=updateQgen[];
	If[Length[pos]==0 || !qLimit,Return[True];];
	If[Length[pos]==1,If[MemberQ[avGen,pos[[1,2]]],If[info>3,Print["Only slack Gen Q violation. Stop"];];Return[True];];];
	pqGenRule=pqGenRule//Normal;
	For[itr=1,itr<=Length[pos],itr++,
		num=pos[[itr,2]];
		genI=genPara[[num,2]];
		bGtMax=pos[[itr,1]]==1;
		If[info>3,Print["Itr ",iter,". Gen ",genI,", Q ",If[bGtMax,"overlimit ","underlimit "],Insert[genPara[[num,{9,8}]],qGenA[[num]]/.pqGenRule,2]];];
		pqGenRule[[2num,2]]=genPara[[num,If[bGtMax,8,9]]];
		pvBus=Complement[pvBus,{genPara[[num,1]]}];
		pqBus=Union[pqBus,{genPara[[num,1]]}];
		pvGen=Complement[pvGen,{num}];];
	pqGenRule=pqGenRule//Dispatch;False
	]

(**************************************** Newton Power Flow ****************************************)
(* local variables: equPf, varsPf, jacPf, posPf *)

formPfEquNewton[]:=Module[{pos,tmp},avBusRule=avBusRule//Normal;
	pos=Join[2 avBus-1,2 avBus,If[bPolRec,2 pvBus,{}]]//Sort;
	consRule=If[bPolRec,#,Thread[avRecA[[pos]]->pol2rec[#[[All,2]]]]]&[avBusRule[[pos]]]//Dispatch;
	posPf=Complement[Range[2 nBus],pos];
	equPf=If[bPolRec,pfEquTot,tmp=((voltReA[[#]]^2+voltImA[[#]]^2-voltA[[#]]^2)&/@pvBus)/.avBusRule[[2 pvBus]];
		ReplacePart[pfEquTot,Thread[(2pvBus)->tmp]]][[posPf]]/.yRule/.kxfmRule/.axfmRule/.pqLoadRule/.pqGenRule/.consRule//Expand//Chop;
	varsPf=avRecA[[posPf]];
	jacPf=D[equPf,{varsPf}]//SparseArray;
	If[bPolRec,#,Thread[avRecA[[posPf]]->pol2rec[#[[All,2]]]]]&[avBusRule[[posPf]]]//Dispatch
	]

solvePflowNewton[info_:5,errTol_:10^-8,maxItr_:50,errMax_:10^8]:=Module[{rsl,rhs,err,itr,pos,vnew},
	If[info>5,rsl=Table[0,{maxItr}];];
	If[info>1,timeBegin=TimeUsed[];];
	varsRule=formPfEquNewton[];vnew=varsPf/.varsRule;
	For[itr=1, itr<=maxItr, itr++,
		rhs=equPf/.varsRule;
		err=Max[Abs[rhs]];
		vnew+=LinearSolve[SparseArray[Most[ArrayRules[jacPf]]/.varsRule], -rhs];
		varsRule=Thread[varsPf->vnew]//Dispatch;
		If[info>5,pos=Position[Abs[rhs],err][[1,1]];rsl[[itr]]={itr,err,Position[avRecA,varsPf[[pos]]][[1,1]]};If[info>7,Print[{itr,err,varsPf[[pos]],rhs[[pos]]}];];];
		If[err>errMax,Print["Divergence! err=",err];Break[];];
		If[err<errTol,avBusRule=If[bPolRec,Thread[avBusA->(avBusA/.consRule/.varsRule)],Thread[avBusA->rec2pol[avRecA/.consRule/.varsRule]]]//Dispatch;
			If[checkLimit[itr,info],Break[];,varsRule=formPfEquNewton[];vnew=varsPf/.varsRule;Continue[];];];
		];
	If[info>1,Print["Power Flow Iteration: ", itr, ", error: ",err,", time used: ",TimeUsed[]-timeBegin,"s"];];
	If[info>5,rsl[[1;;(If[itr>maxItr,maxItr,itr])]],{}]
	]

(**************************************** P-Q Decoupled Power Flow ****************************************)
(* local variables: bpaTot, bqvTot, bpa, bqv, pEquPf, qEquPf, vPos, aPos *)

formPfEquPQ[first_:True]:=Module[{tmp,tmp1,tmp2},
	If[first,tmp=Table[0,{nBus}];
		(tmp[[#[[1]]]]+=#[[7]]+I #[[8]];)&/@busPara;
		(tmp[[#[[1]]]]+=I #[[8]];tmp[[#[[2]]]]+=I #[[8]];)&/@linePara;
		(tmp1=1/(#[[6]]+I #[[7]]);tmp[[#[[1]]]]+=tmp1 (1-#[[8]])/#[[8]]^2+#[[17]]+I #[[18]];tmp[[#[[2]]]]+=tmp1 (#[[8]]-1)/#[[8]])&/@kxfmPara;
		(tmp1=1/(#[[6]]+I #[[7]]);tmp2=(Cos[#[[9]]]-I Sin[#[[9]]])/#[[8]];tmp[[#[[1]]]]+=tmp1(1/#[[8]]^2-tmp2)+#[[17]]+I #[[18]];tmp[[#[[2]]]]+=tmp1(1-tmp2))&/@axfmPara;
		bpaTot=Im[yMatrix-DiagonalMatrix[tmp]]//Chop//SparseArray;
		bqvTot=SparseArray[(#[[1]]->Im[#[[2]]])&/@Most[ArrayRules[yMatrix]],{nBus,nBus}];
		bpa=Fold[Drop[#1,{#2},{#2}]&,bpaTot,Sort[avBus,Greater]];
		aPos=Fold[Drop[#1,{#2}]&,Table[i,{i,nBus}],avBus];
		pEquPf=pfEquTot[[2aPos-1]]/.pqGenRule/.pqLoadRule/.yRule;
		];
	tmp=Sort[avBus~Join~pvBus,Greater];
	If[Length[tmp]==nBus,bqv=qEquPf={};vPos={1};,
		bqv=Fold[Drop[#1,{#2},{#2}]&,bqvTot,tmp];
		vPos=Fold[Drop[#1,{#2}]&,Table[i,{i,nBus}],tmp];
		qEquPf=pfEquTot[[2vPos]]/.pqGenRule/.pqLoadRule/.yRule;
		];
	]

solvePflowPQ[info_:5,errTol_:10^-8,maxItr_:100,errMax_:10^8]:=Module[{rsl,itr,anew,pRhs,pErr,vnew,qRhs,qErr,err},
	If[info>5,rsl=Table[0,{maxItr}];];
	If[info>1,timeBegin=TimeUsed[];];
	formPfEquPQ[True];
	anew=anglA/.avBusRule;
	vnew=voltA/.avBusRule;
	For[itr=1, itr<=maxItr, itr++,
		pRhs=pEquPf/vnew[[aPos]]/.avBusRule;
		anew[[aPos]]-=LinearSolve[bpa,pRhs]/vnew[[aPos]];
		pErr=Max[Abs[pRhs]];
		If[qEquPf=={},qRhs={0};qErr=0;,
			qRhs=qEquPf/vnew[[vPos]]/.avBusRule;
			vnew[[vPos]]-=LinearSolve[bqv,qRhs];
			qErr=Max[Abs[qRhs]];];
		avBusRule=Riffle[Thread[anglA->anew],Thread[voltA->vnew]]//Dispatch;
		err=Max[pErr,qErr];
		If[info>5,rsl[[itr]]={itr,err,0,pErr,aPos[[Position[Abs[pRhs],pErr][[1,1]]]],qErr,vPos[[Position[Abs[qRhs],qErr][[1,1]]]]};rsl[[itr,3]]=rsl[[itr,If[err==pErr,5,7]]];If[info>7,Print[rsl[[itr]]];];];
		If[err>errMax,Print["Divergence! err=",err];Break[];];
		If[err<errTol,If[checkLimit[itr,info],Break[];,formPfEquPQ[False];Continue[];];];
		];
	If[info>1,Print["Power Flow Iteration: ", itr, ", error: ",err,", time uesd: ",TimeUsed[]-timeBegin,"s"];];
	If[info>5,rsl[[1;;(If[itr>maxItr,maxItr,itr])]],{}]
	]

(**************************************** GS Power Flow, 222222 Slow ****************************************)

solvePflowGS[info_:5,errTol_:10^-4,maxItr_:500,errMax_:10^8]:=Module[{rsl,pqLoadVal,pqCjtSym,pqCjtVal,avBusVal,itr,iBus,vold,vnew,pvb,pvp,err},
	If[info>5,rsl=Table[0,{maxItr}];];
	If[info>1,timeBegin=TimeUsed[];];
	pqLoadVal=Table[0,{nBus}];
	(pqLoadVal[[#[[1]]]]+=#[[4]]+I #[[5]])&/@loadPara;
	pqCjtSym=-Conjugate[pqLoadVal];
	MapIndexed[(pqCjtSym[[#1]]+=pGenA[[First[#2]]]-I qGenA[[First[#2]]];)&,genPara[[All,1]]];
	pqGenRule=pqGenRule//Normal;
	avBusVal=voltA Exp[I anglA]/.avBusRule;
	For[itr=1,itr<=maxItr,itr++,vold=avBusVal;
		For[iBus=1,iBus<=nBus,iBus++,
			If[MemberQ[avBus,iBus],Continue[];];
			pvb=MemberQ[genPara[[pvGen,1]],iBus];
			If[pvb,pqCjtVal=Im[avBusVal[[iBus]]Conjugate[yMatrix[[iBus]].avBusVal]+pqLoadVal[[iBus]]];
				pvp=Position[genPara[[All,1]],iBus][[1,1]];
				pqGenRule[[2pvp,2]]=pqCjtVal;];
			pqCjtVal=pqCjtSym[[iBus]]/.pqGenRule;
			vnew=(pqCjtVal/Conjugate[avBusVal[[iBus]]]-Total[Drop[yMatrix[[iBus]]avBusVal,{iBus}]])/yMatrix[[iBus,iBus]];
			avBusVal[[iBus]]=If[pvb,genPara[[pvp,6]]((Cos[#]+I Sin[#])&[Arg[vnew]]),vnew];];
		err=Max[Abs[avBusVal-vold]];
		If[info>5,pvp=Position[Abs[avBusVal-vold],err][[1,1]];rsl[[itr]]={itr,err,busPara[[new2old[[pvp]],2]]};If[info>7,Print[{itr,err,busPara[[new2old[[pvp]],3]],Abs[avBusVal],Arg[avBusVal]/Degree}];];];
		If[err>errMax,Print["Divergence! err=",err];Break[];];
		If[err<errTol,avBusRule=Thread[avBusA->Riffle[Arg[avBusVal],Abs[avBusVal]]]//Dispatch;If[checkLimit[itr,info],Break[];];];
		];(* Gen format:  num I ID PG QG Vset Ireg Qmax Qmin Pmax Pmin a b c *)
	If[itr>maxItr,avBusRule=Thread[avBusA->Riffle[Arg[avBusVal],Abs[avBusVal]]]//Dispatch;];
	If[info>1,Print["Power Flow Iteration: ", itr, ", error: ",err,", time uesd: ",TimeUsed[]-timeBegin,"s"];];
	pqGenRule=pqGenRule//Normal;
	(pqCjtVal=avBusVal[[#]]Conjugate[yMatrix[[#]].avBusVal]+pqLoadVal[[#]];pvp=Position[genPara[[All,1]],#][[1,1]];pqGenRule[[2 pvp,2]]=Im[pqCjtVal];If[MemberQ[avBus,#],pqGenRule[[2 pvp-1,2]]=Re[pqCjtVal];];)&/@(pvBus~Join~avBus);
	pqGenRule=pqGenRule//Dispatch;
	If[info>5,rsl[[1;;(If[itr>maxItr,maxItr,itr])]],{}]
	]

(**************************************** Show Power Flow Result ****************************************)

formBrchFlowEqu[k_,brch_,shunt_:True]:=Module[{targ,from,to,vfrom,vto,pq},
	targ=Switch[brch,1,linePara[[Abs[k]]],2,kxfmPara[[Abs[k]]],_,axfmPara[[Abs[k]]]];
	from=targ[[1]];to=targ[[2]];
	vfrom=Switch[brch,1,#,2,#/kxfmA[[Abs[k]]],_,#/axfmA[[Abs[k],1]]/(Cos[axfmA[[Abs[k],2]]]+I Sin[axfmA[[Abs[k],2]]])]&[voltA[[from]] (Cos[#]+I Sin[#])&[anglA[[from]]]];
	vto=voltA[[to]] (Cos[#]+I Sin[#])&[anglA[[to]]];
	If[k<0,{vfrom,vto}={vto,vfrom};];
	pq=vfrom Conjugate[vfrom-vto]/(targ[[6]] - I targ[[7]]);
	Which[shunt && brch==1,pq+=-I targ[[8]]vfrom Conjugate[vfrom] ;,
		shunt && brch!=1&&k>0 ,pq+=(targ[[17]]-I targ[[18]])vfrom Conjugate[vfrom] If[brch==2,kxfmA[[Abs[k]]]^2,axfmA[[Abs[k],1]]^2];];
	(TrigReduce[#]&/@ComplexExpand[{Re[pq],Im[pq]}])//Chop
	]

brchInfoPrint[info_:5]:=Module[{tmp},If[info<=7,Return[];];(* I J pI qI pJ qJ pLossI pLossJ *)
	If[nLine>0,tmp=Table[Join[formBrchFlowEqu[i,1],formBrchFlowEqu[-i,1]]/.yRule/.avBusRule,{i,nLine}];
		Print["Line: ",MatrixForm[Transpose[{linePara[[All,3]],linePara[[All,4]],tmp[[All,1]],tmp[[All,2]],tmp[[All,3]],tmp[[All,4]],tmp[[All,1]]+tmp[[All,3]],tmp[[All,2]]+tmp[[All,4]]}]]];];
	If[nKxfm>0,tmp=Table[Join[formBrchFlowEqu[i,2],formBrchFlowEqu[-i,2]]/.yRule/.kxfmRule/.axfmRule/.avBusRule,{i,nKxfm}];
		Print["Kxfm: ",MatrixForm[Transpose[{kxfmPara[[All,3]],kxfmPara[[All,4]],tmp[[All,1]],tmp[[All,2]],tmp[[All,3]],tmp[[All,4]],tmp[[All,1]]+tmp[[All,3]],tmp[[All,2]]+tmp[[All,4]]}]]];];
	If[nAxfm>0,tmp=Table[Join[formBrchFlowEqu[i,3],formBrchFlowEqu[-i,3]]/.yRule/.kxfmRule/.axfmRule/.avBusRule,{i,nAxfm}];
		Print["Axfm: ",MatrixForm[Transpose[{axfmPara[[All,3]],axfmPara[[All,4]],tmp[[All,1]],tmp[[All,2]],tmp[[All,3]],tmp[[All,4]],tmp[[All,1]]+tmp[[All,3]],tmp[[All,2]]+tmp[[All,4]]}]]];];
	]

busInfoPrint[info_:5]:=Module[{tmp,tmp1},If[info<=1,Return[];];(* I name type volt vflag angl GL BL pLoad qLoad pGen pflag qGen qflag *)
	tmp=Table[0,{nBus},{14}];
	tmp[[All,{1,2,7,8}]]=busPara[[new2old,{2,3,7,8}]];
	tmp[[All,3]]=ReplacePart[Table[1,{nBus}],Thread[pvBus->Table[2,{Length[pvBus]}]]~Join~Thread[avBus->Table[3,{Length[avBus]}]]];
	tmp[[All,4]]=voltA/.avBusRule;
	tmp[[All,5]]=MapIndexed[Which[#1<busPara[[new2old[[#2[[1]]]],12]],"-",#1>busPara[[new2old[[#2[[1]]]],11]],"+",True,""]&,tmp[[All,4]]];
	tmp[[All,6]]=anglA/Degree/.avBusRule;
	tmp1=Table[0,{nBus}];
	tmp[[All,9]]=ReplacePart[tmp1,Thread[loadPara[[All,1]]->pLoadA/.pqLoadRule]];
	tmp[[All,10]]=ReplacePart[tmp1,Thread[loadPara[[All,1]]->qLoadA/.pqLoadRule]];
	tmp[[All,11]]=ReplacePart[tmp1,Thread[genPara[[All,1]]->pGenA/.pqGenRule]];
	tmp[[All,13]]=ReplacePart[tmp1,Thread[genPara[[All,1]]->qGenA/.pqGenRule]];
	tmp[[All,12]]=ReplacePart[Table["",{nBus}],Thread[genPara[[All,1]]->MapIndexed[(Which[#1<genPara[[#2[[1]],11]],"-",#1>genPara[[#2[[1]],10]],"+",True,""])&,pGenA/.pqGenRule]]];
	tmp[[All,14]]=ReplacePart[Table["",{nBus}],Thread[genPara[[All,1]]->MapIndexed[(Which[#1<genPara[[#2[[1]],9]],"-",#1>genPara[[#2[[1]],8]],"+",True,""])&,qGenA/.pqGenRule]]];
	Print[MatrixForm[tmp[[busPara[[All,1]],All]]]];
	]

solvePf[info_:5]:=Module[{rslPf,figA,figB},
	Which[
		pfSolMd=="GSeidel",If[info>1,Print["Gauss-Seidel Power Flow ##############"];];(* 222222 Slow *)
			rslPf=solvePflowGS[info,errTolGs,maxIterGs,errMax];,
		pfSolMd=="PQfast",If[info>1,Print["P-Q Decouple Power Flow ##############"];];
			rslPf=solvePflowPQ[info,errTolPQ,maxIterPQ,errMax];,
		pfSolMd=="NewtonPol"||pfSolMd=="NewtonRec",If[info>1,Print["Newton Power Flow in ",If[bPolRec,"Polar","Rectangle"]," Coordinates ##############"];];
			rslPf=solvePflowNewton[info,errTol,maxIter,errMax];,
		True,If[pfSolMd=="DcPowerFlow",Input["Use dcPowerFlow[] pls."];,Input["Unknown pfSolMd method: ",pfSolMd,"! Quit."];Quit[];];
		];
	busInfoPrint[info];brchInfoPrint[info];
	If[info>7 && Length[rslPf]>1,
		figA=ListLogPlot[rslPf[[All,{1,2}]],AxesLabel->{"Itr","Err"},PlotStyle->Red,PlotRange->All];
		figB=ListPlot[rslPf[[All,{1,3}]],AxesLabel->{"Itr","2*Bus"},PlotStyle->Red,PlotRange->All];
		Print[GraphicsRow[{figA,figB},ImageSize->800]];];
	]


(**************************************** DC Power Flow ****************************************)
(* local variables: yDcMatrix, brchDcPara *)

formYdcMatrix[info_:5]:=Module[{nBrch,aInMat},
	nBrch=nLine+nKxfm;
	brchDcPara=Join[If[nLine==0,{},Transpose[{linePara[[All,1]],linePara[[All,2]],1/ linePara[[All,7]]}]],If[nKxfm==0,{},Transpose[{kxfmPara[[All,1]],kxfmPara[[All,2]],1/ kxfmPara[[All,7]]}]]];
	aInMat=SparseArray[Flatten[MapIndexed[{{#1[[1]],First[#2]}->1,{#1[[2]],First[#2]}->-1}&,brchDcPara],1],{nBus,nBrch}];
	yDcMatrix=aInMat.DiagonalMatrix[brchDcPara[[All,3]]].Transpose[aInMat]//Chop//SparseArray;
	If[info>7,Print["yDcMatrix formed."];If[info>12,Print[MatrixForm[brchDcPara]];Print[MatrixForm[yDcMatrix]];];];
	]

definePfDcSym[info_:5]:=Module[{},
	avBus=Flatten[Position[busPara[[new2old,4]],3]];
	avGen=Flatten[Position[genPara[[All,1]],#]&/@avBus];

	anglDcA=ToExpression["a"<>#]&/@busName;
	pGenDcA=ToExpression["pG"<>#]&/@genName;
	pLoadDcA=If[nLoad==0,{},ToExpression["pL"<>#]&/@loadName];

	anglDcRule=Thread[anglDcA->(busPara[[new2old,10]]Degree)];
	pGenDcRule=Thread[pGenDcA->genPara[[All,4]]];
	pGenDcRule[[avGen,2]]-=Total[genPara[[All,4]]]-Total[loadPara[[All,4]]];
	pLoadDcRule=If[nLoad==0,{},Thread[pLoadDcA->loadPara[[All,4]]]];
	If[info>7,Print["Power Flow Symbols defined."]];
	]

formPfEquDc[info_:5]:=Module[{pDcA},
	yMat=Drop[yDcMatrix,avBus,avBus];
	pDcA=Table[0,{nBus}];
	MapIndexed[(pDcA[[#1]]+=pGenDcA[[First[#2]]];)&,genPara[[All,1]]];
	If[nLoad!=0,MapIndexed[(pDcA[[#1]]-=pLoadDcA[[First[#2]]];)&,loadPara[[All,1]]];];
	pRgt=Drop[pDcA,avBus]/.pGenDcRule/.pLoadDcRule;
	]

dcPfInfoPrint[info_:5]:=Module[{tmp},
	If[info>1,(* I name type angl pLoad pGen pflag *)
		tmp=Table[0,{nBus},{7}];tmp[[All,{1,2,3}]]=busPara[[new2old,{2,3,4}]];
		tmp[[All,4]]=anglDcA/Degree/.anglDcRule;
		tmp[[All,5]]=ReplacePart[tmp[[All,7]],Thread[loadPara[[All,1]]->pLoadDcA/.pLoadDcRule]];
		tmp[[All,6]]=ReplacePart[tmp[[All,7]],Thread[genPara[[All,1]]->pGenDcA/.pGenDcRule]];
		tmp[[All,7]]=ReplacePart[Table["",{nBus}],Thread[genPara[[All,1]]->MapIndexed[(Which[#1<
		genPara[[#2[[1]],11]],"-",#1>genPara[[#2[[1]],10]],"+",True,""])&,pGenDcA/.pGenDcRule]]];
		Print[MatrixForm[tmp[[busPara[[All,1]],All]]]];];
	If[info>7,(* I J p *)
		tmp={new2old[[#[[1]]]],new2old[[#[[2]]]],#[[3]],(anglDcA[[#[[1]]]]-anglDcA[[#[[2]]]])#[[3]]/.anglDcRule}&/@brchDcPara//Chop;
		Print[MatrixForm[tmp]];];
	]

dcPowerFlow[info_:5]:=Module[{},
	If[info>1,Print["DC Power Flow ##############"];];
	formYdcMatrix[info];
	definePfDcSym[info];
	formPfEquDc[info];
	anglDcRule[[Complement[Range[nBus],avBus],2]]=LinearSolve[yMat,pRgt]+anglDcRule[[avBus[[1]],2]];
	dcPfInfoPrint[info];
	]



busRslAcDcCmp[]:=Module[{tmp,tmp1},tmp1=Table[0,{nBus}];(* I name type volt vflag angl GL BL pLoad qLoad pGen pflag qGen qflag *)
	If[Head[avBusRule]==Symbol,Print["busRslAcDcCmp[] Need AC Power Flow!"];Return[];];
	tmp=Table[0,{nBus},{17}];
	tmp[[All,{1,2,7,8}]]=busPara[[new2old,{2,3,7,8}]];
	tmp[[All,3]]=ReplacePart[Table[1,{nBus}],Thread[pvBus->Table[2,{Length[pvBus]}]]~Join~Thread[avBus->Table[3,{Length[avBus]}]]];
	tmp[[All,4]]=voltA/.avBusRule;
	tmp[[All,5]]=MapIndexed[Which[#1<busPara[[new2old[[#2[[1]]]],12]],"-",#1>busPara[[new2old[[#2[[1]]]],11]],"+",True,""]&,tmp[[All,4]]];
	tmp[[All,6]]=anglA/Degree/.avBusRule;
	tmp[[All,9]]=ReplacePart[tmp1,Thread[loadPara[[All,1]]->pLoadA/.pqLoadRule]];
	tmp[[All,10]]=ReplacePart[tmp1,Thread[loadPara[[All,1]]->qLoadA/.pqLoadRule]];
	tmp[[All,11]]=ReplacePart[tmp1,Thread[genPara[[All,1]]->pGenA/.pqGenRule]];
	tmp[[All,13]]=ReplacePart[tmp1,Thread[genPara[[All,1]]->qGenA/.pqGenRule]];
	tmp[[All,12]]=ReplacePart[Table["",{nBus}],Thread[genPara[[All,1]]->MapIndexed[(Which[#1<genPara[[#2[[1]],11]],"-",#1>genPara[[#2[[1]],10]],"+",True,""])&,pGenA/.pqGenRule]]];
	tmp[[All,14]]=ReplacePart[Table["",{nBus}],Thread[genPara[[All,1]]->MapIndexed[(Which[#1<genPara[[#2[[1]],9]],"-",#1>genPara[[#2[[1]],8]],"+",True,""])&,qGenA/.pqGenRule]]];
	tmp[[All,15]]=anglDcA/Degree/.anglDcRule;
	tmp[[All,16]]=tmp[[All,15]]-tmp[[All,6]];
	tmp[[All,17]]=If[#[[1]]==0,0,(#[[2]]-#[[1]])/#[[1]]100]&/@Transpose[{tmp[[All,6]],tmp[[All,15]]}];
	Print[MatrixForm[tmp[[busPara[[All,1]],All]]]];
	Print["max err: Abs = ",Max[Abs[tmp[[All,6]]-tmp[[All,15]]]],", Pct = ",Max[Abs[tmp[[All,17]]]]];
	Print["Slack bus ",new2old[[avBus]]," : DC = ",#1,", AC = ",#2, ";\t err Abs = ",#1-#2,", Pct = ",If[#2==0,0,(#1-#2)/#2 100] ]&[pGenDcA[[avGen[[1]]]]/.pGenDcRule,pqGenA[[2avGen[[1]]-1]]/.pqGenRule];
	figA=ListPlot[{Transpose[{new2old,tmp[[All,6]]}],Transpose[{new2old,tmp[[All,15]]}]},AxesLabel->{"Bus","a"},PlotStyle->{Red,Blue},PlotRange->All];
	figB=ListPlot[Transpose[{new2old,tmp[[All,17]]}],AxesLabel->{"Bus","Err(%)"},PlotStyle->Red,PlotRange->All];
	Print[GraphicsRow[{figA,figB},ImageSize->800]];
	]

brchRslAcDcCmp[]:=Module[{dc,tmp,tmp1,tmp2},(* I J pI qI pJ qJ pLossI pLossJ *)
	If[Head[avBusRule]==Symbol,Print["brchRslAcDcCmp[] Need AC Power Flow!"];Return[];];
	dc=((anglDcA[[#[[1]]]]-anglDcA[[#[[2]]]])#[[3]]/.anglDcRule)&/@brchDcPara//Chop;
	If[nLine>0,tmp=dc[[1;;nLine]];
		tmp1=Table[Join[formBrchFlowEqu[i,1],formBrchFlowEqu[-i,1]]/.yRule/.avBusRule,{i,nLine}];
		tmp2=If[#[[2]]==0,0,(#[[1]]-#[[2]])/#[[2]]100]&/@Transpose[{tmp,tmp1[[All,1]]}];
		Print["Line: ",MatrixForm[Transpose[{linePara[[All,3]],linePara[[All,4]],tmp1[[All,1]],tmp1[[All,2]],tmp1[[All,3]],tmp1[[All,4]],tmp1[[All,1]]+tmp1[[All,3]],tmp1[[All,2]]+tmp1[[All,4]],tmp,tmp-tmp1[[All,1]],tmp2}]]];
		Print["max err: Abs = ",Max[Abs[tmp-tmp1[[All,1]]]],", Pct = ",Max[Abs[tmp2]]];
		figA=ListPlot[{Transpose[{Range[nLine],tmp}],Transpose[{Range[nLine],tmp1[[All,1]]}]},AxesLabel->{"Line","P"},PlotStyle->{Red,Blue},PlotRange->All];
		figB=ListPlot[Transpose[{Range[nLine],tmp2}],AxesLabel->{"Line","Err(%)"},PlotStyle->Red,PlotRange->All];
		Print[GraphicsRow[{figA,figB},ImageSize->800]];
		];
	If[nKxfm>0,tmp=dc[[nLine+1;;]];
		tmp1=Table[Join[formBrchFlowEqu[i,2],formBrchFlowEqu[-i,2]]/.yRule/.kxfmRule/.axfmRule/.avBusRule,{i,nKxfm}];
		tmp2=If[#[[2]]==0,0,(#[[1]]-#[[2]])/#[[2]]100]&/@Transpose[{tmp,tmp1[[All,1]]}];
		Print["Kxfm: ",MatrixForm[Transpose[{kxfmPara[[All,3]],kxfmPara[[All,4]],tmp1[[All,1]],tmp1[[All,2]],tmp1[[All,3]],tmp1[[All,4]],tmp1[[All,1]]+tmp1[[All,3]],tmp1[[All,2]]+tmp1[[All,4]],tmp,tmp-tmp1[[All,1]],tmp2}]]];
		Print["max err: Abs = ",Max[Abs[tmp-tmp1[[All,1]]]],", Pct = ",Max[Abs[tmp2]]];
		figA=ListPlot[{Transpose[{Range[nKxfm],tmp}],Transpose[{Range[nKxfm],tmp1[[All,1]]}]},AxesLabel->{"Kxfm","P"},PlotStyle->{Red,Blue},PlotRange->All];
		figB=ListPlot[Transpose[{Range[nKxfm],tmp2}],AxesLabel->{"Kxfm","Err(%)"},PlotStyle->Red,PlotRange->All];
		Print[GraphicsRow[{figA,figB},ImageSize->800]];
		];
	]

(**************************************** Note ****************************************
1. Rectange power flow only applies to one slack bus
2. How about multiple gen or load at same bus

*)

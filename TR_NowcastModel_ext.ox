/*****************************************************************************************************************************************************
Hamza Demircan

Improving Density Nowcasting of GDP using Survey of Professional Forecasters
*****************************************************************************************************************************************************/
#include <oxstd.h>
#include <oxprob.h>
//#include <packages/gnudraw/gnudraw.h>
#include <oxdraw.h>
#include <oxfloat.h>
#include <arma.h>
#import <maximize>
#import <database>
#import <solvenle>
 #import <CHOLRobust>
#import <CHOLBack>
#import <SV_Part_GIS44m>
//#import <SV_Part_GIS_NoSurvey>
//#import <SV_Part_GIS4>

static decl nonNan, mmnt, SV_fac, SV_gdp, SV_m, var_m_t, std_rt, frcst, hrzn, res_gdp, ht_gdp, ht_gdpT, var_gdp, doft_f, omt, omt_gdp, inf_, inf_pr, R_;
static decl yy, yy_gdp,yy_gdp_stndrdzd, wrkng_days, yy1_gr, nov, mBtTm, dSampleT, mMVAL, freq, vfreqY, vTypeIY, vTypeIIY, vTypeIIIY,freq_, vfreqY_, vTypeIY_, vTypeIIY_, vTypeIIIY_;
static decl mlambdam_st, mlambdam_m_st, mPhim, mVarStm, vVarym, nolf, nolfq, nolsq, nolfm;
static decl save, printorder, printorder2, printorder_mh, draworder, tres, StateSel, lagof, dof_er, scale_er;
static decl data_name, data_freq, data_typeI, data_typeII, data_typeIII, data_trans, data_Qahead,
selection, selection_, selection_V, selection_M,selection_M2, selection_pr ,selection_name, selection_in, mKSQ,  mY_mean, mY_stddev, facnu, StDev_in_Standardization, slope_l, std_l, meany_l, indy_l; // yy1_gro;

static decl XtT0SV, 		PtT0SV, 		dSigSV, 		dPhiSV, 		dMuSV, 			vSigmay_vl,			vh_gdp,		vh_gdp_frcst,
			XtT0SV_f, 		PtT0SV_f, 		dSigSV_f, 		dPhiSV_f, 		dMuSV_f, 		vSigmay_vl_f,		vh_f,		vh_f_frcst,
			XtT0SV_m, 		PtT0SV_m, 		dSigSV_m, 		dPhiSV_m, 		dMuSV_m, 		vSigmay_vl_m,		vh_m,		vh_m_frcst;
			
			
static decl MHphi_acc, aIndex, dimf, kq_t, kq_t_k, km_t, km_t_k,n_q, n_qf, n_qfh, n_qfs, n_qfs1, n_qs, n_m, no_vec, number_fb,
vlambdam_rgdp, mlambdam_qf, mlambdam_qs, mlambdam_m, vVarym_qf, vVarym_rgdp, vVarym_qs, vVarym_m, yy_star_nowcast, yy_nowcast, yy_forecast, Start_t0;



 
/****************************************TABLE*******************************************************/
table(variables)
	{
	decl size   = columns(variables)                  ;
	decl meann  = meanc(variables)'                   ;
	decl stdev  = sqrt(varc(variables))'              ;
	decl band   = zeros(size,2)                       ;

	for(decl i=0;i<size;i++)
	{
		band[i][0]  = meann[i]-1.96*stdev[i]      ;
		band[i][1]  = meann[i]+1.96*stdev[i]      ;
	}
							
	decl tabl   = zeros(size,2)                       ;

	for(decl i = 0; i<size;i++)
	{
		tabl[i][]= meann[i]~stdev[i]			  ;
	}							   
return tabl;							   
}
/****************************************TABLE*******************************************************/







/**************************TRANSFORM_DATA***************************************************************************************/
TRANSFORM_DATA(data, const novv, const dataname, const selection, const freq)
{
decl slope = zeros(1,novv);  //First row for linear trend which is the constant term for the first difference
decl std   = zeros(1,novv);
decl meany = zeros(1,novv);
decl indy  = zeros(1,novv);
decl i;

decl yy1_gr 	= mMVAL*ones(dSampleT, novv);

for(i=0; i<novv; i++)
	{
	   decl tmp, difindex;
	   decl index       = vecindex(data[][i] .!= mMVAL);      //println(index);
			if (index==<>){
				data[][i]       = mMVAL*ones(dSampleT, 1);
				yy1_gr[][i] 	= mMVAL*ones(dSampleT, 1);
					      }
			else{
					if(  (data_trans[ selection[i] ] == "G") )
						{
							tmp         = data[index][i];				     //if (i==6){println(tmp);}
							difindex    = index[1:][];						  
	         				tmp         = 100*diff0(log(tmp),1)[1:][];		 //if (i==6){println(tmp);}
						}
					else if(  (data_trans[ selection[i] ] == "L") )
						{
							tmp         = data[index][i];
							difindex    = index[0:][];						  
	         				tmp         = tmp;
						}
					else if(  (data_trans[ selection[i] ] == "D") )
						{
							tmp         = data[index][i];				  
							difindex    = index[1:][];						  
	         				tmp         = diff0(tmp,1)[1:][]*100;		 //if(i==14){println(tmp);}
						}

					decl tmp2        = tmp;
					decl Ttmp        = sizer(tmp);
					decl Ttmp22      = sizer(tmp)-0;	  //3
					decl tmp22       = tmp[:Ttmp22-1];

					 meany[i]        = meanc(tmp22);                     	  //println(" meany[i] ",meany[i]);
	 		 		 indy[i]         = sizer(index);
 
					decl ltrend22    = range(1, Ttmp22, 1)'; 
					decl tmpx22      = ones(Ttmp22,1);//~ltrend~qtrend;
					decl beta        = invertsym(tmpx22'tmpx22)*tmpx22'*tmp22;
					
					decl ltrend      = range(1, Ttmp, 1)';  decl qtrend = sqr(ltrend); 
					decl tmpx        = ones(Ttmp,1);//~ltrend~qtrend;
//					decl beta        = invertsym(tmpx'tmpx)*tmpx'*tmp;	         //println("beta ", beta, "meany[i] ", meany[i] );   //println("tmp   ", tmp);	  
						 tmp         = tmp - tmpx*beta;		                     //println("tmp   ", tmp);
	 		 			 slope[i]    = beta;
	 		 			 std[i]      = moments(tmp22)[2];

/***********************STD******************************************************************************************************/
					if(StDev_in_Standardization == 0)
					{
						if( (data_typeII[ selection[i] ]=="S")||(i==0) )                 //(i==1)||(i==1)||(i==2)||(i==3)||(i==4) )
					    {
							tmp = tmp; 			//println(data_typeII[selection[i]] , " data_typeII[selection[i]] ", " i ",i);
						}
						else
						{
						tmp = tmp./std[i];			  /****Use (detrended) STANDARDIZED DATA ******/
						}					   	
					}
/***********************STD******************************************************************************************************/
					else
						{
						tmp = tmp./std[i];			  /****Use (detrended) STANDARDIZED DATA ******/
						}					   	
			
					if( (data_typeII[ selection[i] ]=="S") )                 //(i==1)||(i==1)||(i==2)||(i==3)||(i==4) )
			    		{
					tmp = 1*tmp; 			//println(data_typeII[selection[i]] , " data_typeII[selection[i]] ", " i ",i);
						}

     				data[][i]   		= mMVAL*ones(dSampleT, 1);
     				data[difindex][i]	= tmp;
					yy1_gr[][i]   		= mMVAL*ones(dSampleT, 1);
		    		yy1_gr[difindex][i]	= tmp2;	 //println(" tmp2 ", tmp2, " tmp ", tmp);
			} // else
	}	   // for(i=0; i<novv; i++)

return {data[0:][], slope, std, meany, indy, yy1_gr[0:][]};
}
/**************************TRANSFORM_DATA***************************************************************************************/







/****************SAMPLE_SIGMAY**************************************************************************************************************/
SAMPLE_SIGMAY(const res, const Sigma2y_dof_, const Sigma2y_Scale_, const j)
{
	decl ress = res[Start_t0:];
	decl tstar = sizer(ress);
	decl dof   = Sigma2y_dof_   +  tstar;
	decl Scale = Sigma2y_Scale_ + ress'ress;
	decl mCtt  = sqrt(Scale)';
	
	decl dSigy;
	decl accept=0; decl i;
	 	for(i=0; accept!=1; i++)					 
		{
	    	decl mU    = rann(dof,1);
	        dSigy = mCtt'*(mU'mU)^(-1)*mCtt;
			//if (dSigy> 1)
			//{/*println("---------------------------PHI Unit Root-----------------------------------");*/	 continue;}
		 	accept=1;
		}
return dSigy;
}
/****************SAMPLE_SIGMAY**************************************************************************************************************/







/****************CONSTRUCTING MEASUREMENT EQUATION MATRİCES-TIME VARYING PART******************************************************************/
CONSTRUCT_MEAS_TIME(H, const vlambdam_rgdp_)			   // if(returnval == 1) => calculate errors for the part calculated by MH and return the variances of it 
{
	decl H_t_1, H_t_3; 
/**********************************************************    t= 2    **********************************************************/
	decl H_t_2 = H;
	decl dimension1;

	if(n_qfs1>0)
	{
		dimension1 = <1;4;7;10;13>;
		dimension1 = dimension1[:n_qfs1-1];
	}	

	decl wti_kq_f = <1,2,3,2,1>.*3/3;
	decl wti_kq_s = <1,1,1>.*3/3;

	if(n_qfs1>0)
		{
		    for(decl d1 = 0; d1<rows(dimension1); d1++)
			{
				decl func_phi, temp;

			  	if(dimension1[d1]==1)
			  		{
		      			func_phi = mPhim* (3/3);   //println(	" d1 ", d1, " func_phi ",func_phi);
			  		}   // if(dimension1[d1]==1) 

			    else 
			  		{
						func_phi	= zeros(facnu, facnu); 
						temp 		= unit(facnu)*mPhim^(dimension1[d1]-5);

						decl coeffs = reverser(wti_kq_f);                 //println( 	" d1 ", d1, " coeffs ",coeffs);
						for(decl l = 0; l<5; l++)
							{	
								temp 		= temp*mPhim;                 //println( " l ", l, " temp ", temp, " wti_kq_f[l] ", wti_kq_f[l]);
								func_phi 	= func_phi + coeffs[l]*temp;  //println(" func_phi ",func_phi);
							}	  // for l	
					}   //  else 
		  
				H_t_2[n_qfh + d1] [(2*facnu)+(2*facnu)*nolfq + (1*facnu)+(1*facnu)*nolsq: (2*facnu)+ (2*facnu)*nolfq + (1*facnu)+ (1*facnu)*nolsq +1*facnu-1] = vlambdam_rgdp_*func_phi;	 //println(" vlambdam_rgdp_*func_phi ", vlambdam_rgdp_*func_phi);

				if(d1 == 0)		   // For more than 1 quarter ahead survey, we can not use the information of current aggregated(daily to quarterly) factor, we just iterate the daily factor, and aggregate this to match quarterly released survey
					{
						H_t_2[n_qfh + d1] [0 : 1*facnu-1] 		= vlambdam_rgdp_;	 //println(" vlambdam_rgdp ",vlambdam_rgdp);		// H[n_qfh + d] [0] = vlambdam_rgdp;	
					}  // if(d1 == 0)	
			} //for(decl d1 = 0; d1<rows(dimension1); d1++)
		}  //if(n_qfs1>0)
/**********************************************************    t= 2    **********************************************************/


/**********************************************************    t= 1    **********************************************************/
H_t_1 = H;

	if(n_qfs1>0)
	{	dimension1 = <2;5;8;11;14>;
		dimension1 = dimension1[:n_qfs1-1];	}
/*******************************************************************************************************************************************/
if(n_qfs1>0)
{	for(decl d1 = 0; d1<rows(dimension1); d1++)
	{	decl func_phi, temp;

		  if(dimension1[d1]==2)
		  {
		      func_phi = (mPhim^2 + 2*mPhim)* (3/3);   //println(	" d1 ", d1, " func_phi ",func_phi);
		  }   // if(dimension1[d1]==1) 

		  else 
		  {	func_phi	= zeros(facnu, facnu); 
			temp 		= unit(facnu)*mPhim^(dimension1[d1]-5);

			decl coeffs = reverser(wti_kq_f);					 //println( 	" d1 ", d1, " coeffs ",coeffs);
				for(decl l = 0; l<5; l++)
				{	
					temp 		= temp*mPhim;				    //println( " l ", l, " temp ", temp, " wti_kq_f[l] ", wti_kq_f[l]);
					func_phi 	= func_phi + coeffs[l]*temp;	//println(" func_phi ",func_phi);
				}	  // for l	
//////		println("-------------------------------------------");
		}   // if(dimension1[d1]>1)
		  
		H_t_1[n_qfh + d1] [(2*facnu)+(2*facnu)*nolfq + (1*facnu)+(1*facnu)*nolsq: (2*facnu)+ (2*facnu)*nolfq + (1*facnu)+ (1*facnu)*nolsq +1*facnu-1] = vlambdam_rgdp_*func_phi;	//println(" vlambdam_rgdp_*func_phi ", vlambdam_rgdp_*func_phi);
			 if         (d1 == 0)		   // For more than 1 quarter ahead survey, we can not use the information of current aggregated(daily to quarterly) factor, we just iterate the daily factor, and aggregate this to match quarterly released survey
			{	H_t_1[n_qfh + d1] [0 : 1*facnu-1] 		= vlambdam_rgdp_;	 //println(" vlambdam_rgdp ",vlambdam_rgdp);		// H[n_qfh + d] [0] = vlambdam_rgdp;	
			}   // else  = 0
	} // d1
}
/////////*****************************************************    t= 1    **********************************************************/


/*************************************************************    t= 3    **********************************************************/
H_t_3 = H;

	if(n_qfs1>0)
	{	dimension1 = <0;3;6;9;12>;
		dimension1 = dimension1[:n_qfs1-1];	}
/*******************************************************************************************************************************************/
if(n_qfs1>0)
{	for(decl d1 = 0; d1<rows(dimension1); d1++)
	{	decl func_phi, temp;

		  if(dimension1[d1]==0)
		  {	  // println( "  if dimension1[d1] ",dimension1[d1] );
		      func_phi = (0)* (3/3);   //println(	" d1 ", d1, " func_phi ",func_phi);
		  }   // if(dimension1[d1]==1) 

		  else if(dimension1[d1]==3)
		  {	  //println( " else if dimension1[d1] ",dimension1[d1] );
		      func_phi = (mPhim^3 + 2*mPhim^2 + 3*mPhim)* (3/3);   //println(	" d1 ", d1, " func_phi ",func_phi);
		  }   // if(dimension1[d1]==1) 

		  else 
		  {	  //		  println( "  else dimension1[d1] ",dimension1[d1] );
		  func_phi	= zeros(facnu, facnu); 
			temp 		= unit(facnu)*mPhim^(dimension1[d1]-5);

			decl coeffs = reverser(wti_kq_f);	//println( 	" d1 ", d1, " coeffs ",coeffs);
				for(decl l = 0; l<5; l++)
				{	
					temp 		= temp*mPhim;                 //println( " l ", l, " temp ", temp, " wti_kq_f[l] ", wti_kq_f[l]);
					func_phi 	= func_phi + coeffs[l]*temp;  //println(" func_phi ",func_phi);
				}	  // for l								  
		}   // if(dimension1[d1]>1)
		  
		H_t_3[n_qfh + d1] [(2*facnu)+(2*facnu)*nolfq + (1*facnu)+(1*facnu)*nolsq: (2*facnu)+ (2*facnu)*nolfq + (1*facnu)+ (1*facnu)*nolsq +1*facnu-1] = vlambdam_rgdp_*func_phi;		//		println(" vlambdam_rgdp_*func_phi ", vlambdam_rgdp_*func_phi);
			 if         (d1 == 0)		   // For more than 1 quarter ahead survey, we can not use the information of current aggregated(daily to quarterly) factor, we just iterate the daily factor, and aggregate this to match quarterly released survey
			{	H_t_3[n_qfh + d1] [0 : 1*facnu-1] 		= vlambdam_rgdp_;	 //println(" vlambdam_rgdp ",vlambdam_rgdp);		// H[n_qfh + d] [0] = vlambdam_rgdp;	
			}   // else  = 0
			 if         (d1 == 1)		   // For more than 1 quarter ahead survey, we can not use the information of current aggregated(daily to quarterly) factor, we just iterate the daily factor, and aggregate this to match quarterly released survey
			{	H_t_3[n_qfh + d1] [1] 		= vlambdam_rgdp_;	 //println(" vlambdam_rgdp ",vlambdam_rgdp);		// H[n_qfh + d] [0] = vlambdam_rgdp;	
			}   // else  = 0
	} // d1
}

return {H_t_1, H_t_2, H_t_3};
}
/****************CONSTRUCTING MEASUREMENT EQUATION MATRİCES-TIME VARYING PART******************************************************************/




/****************CONSTRUCTING MEASUREMENT EQUATION MATRİCES******************************************************************/
CONSTRUCT_MEAS(const vlambdam_rgdp_, const mlambdam)
{
			decl H = zeros(n_qf + n_qs + n_m, dimf);
			
			//println( " n_qf ", n_qf);
			
				for (decl i=0; i<n_qfh; i++)
				{	H[i]          						[0       : 1*facnu-1]         = mlambdam_qf[i][0];
				}
				
				for (decl i=n_q; i<nov; i++)
				{	H[i] [(2*facnu)+(2*facnu)*nolfq + (1*facnu)+(1*facnu)*nolsq : (2*facnu)+ (2*facnu)*nolfq + (1*facnu)+(1*facnu)*nolsq +1*facnu-1] = mlambdam[i-n_qf+1][] ;
				}
			
			if(n_qfs1>0){		H[0]             [0       : 1*facnu-1] = vlambdam_rgdp_	;	}	
			//println(H);
			
			decl R = diag(vVarym);
return {H, R};
}
/****************CONSTRUCTING MEASUREMENT EQUATION MATRICES******************************************************************/







/****************CONSTRUCTING COEFFICIENTS MATRICES******************************************************************/
CONSTRUCT_COEF(const i, const mPhim, const var_factor_t, const returnval, const omt_f)
{		                   // returnval = 1 then return {F1_t, F2_t, Q}
    	 				   // returnval = 2 then return {W_t_kq_f, W_t_km_f, W_t_km_s, W_t_kw_f, W_t_kw_s, 																			  //							I_t_kq_s, I_t_km_f, I_t_km_s, I_t_kw_f, I_t_kw_s}
						decl t = i+1;              // the first value : t=1, this is the the first day after release
						
						decl wti_kq_f = zeros(5,1);
						decl wti_kq_s = zeros(5,1);
																  //println(" k_t :", kq_t[i], " kq_t_k :", kq_t_k[i]);
							 wti_kq_f = <1,2,3,2,1>.*3/3;		  //println("wti_kq_f ", wti_kq_f, " kq_t[i]+kq_t_k[i]-1 ",kq_t[i]+kq_t_k[i]-1);
							 wti_kq_s = <1,1,1>.*3/3;			  //println("wti_kq_f ", wti_kq_f);
						
							 
						/* --------------------------QUARTERLY-----------------------*/
						decl W_t_kq_f, W_t_kq_s, I_t_kq_f, I_t_kq_s, remainder;
						//remainder = imod(kq_t[i]-t,kq_t[i]);
						remainder = imod(3-t,3);   //println( " before remainder ",remainder, " 3-t ", 3-t);
						if(remainder<0) {remainder = remainder+3;}
						else 			{remainder = remainder;}
						//println( " after remainder ",remainder, " 3-t ", 3-t);
						
							 if(remainder==2)                        // (filled2[0][i]==1)
							 {
						//	 	if(i>1){//println( " yy[0][i-1] ",yy[0][i-1], " i ",i);}
						//	 	//println( " filled2[0][i]==1 "," i ", i , " ", " remainder ", remainder );
						//	 	W_t_kq_f = ( -1*unit(facnu) )| (0*unit(facnu));
								W_t_kq_f = ( -1*wti_kq_f[3-1]*unit(facnu) )| (0*unit(facnu));
							 	I_t_kq_f = ( zeros(facnu,facnu)~unit(facnu) )| ( 	zeros(facnu,facnu)~zeros(facnu,facnu) );
						
								W_t_kq_s = -1*unit(facnu);
							 	I_t_kq_s = zeros(facnu,facnu);
							 }
						
							 else 										 // (filled2[0][i]==0)
							 {
						//		//println(" filled2[0][i]==0 ", " i ", i , " ", " remainder ", remainder );
						//	 	W_t_kq_f = ( -1*unit(facnu) ) |  ( 0*unit(facnu) );
								W_t_kq_f = ( -1*wti_kq_f[remainder]*unit(facnu) ) |  ( -1*wti_kq_f[remainder+3]*unit(facnu) ); 
							 	I_t_kq_f = unit(2*facnu);
								
								W_t_kq_s = -1*unit(facnu); 
							 	I_t_kq_s = unit(facnu);									 				
							 }
						/* --------------------------QUARTERLY-----------------------*/
						
						// insert  here---if(returnal == 1){} 				  
						decl F1_t = zeros(dimf, dimf);
						decl F2_t = zeros(dimf, dimf);
						decl Q_t  = zeros(dimf, dimf);
						decl F_t; 
						if(returnval == 1){
						
						//////dimf = (2*facnu)  + (2*facnu)*nolfq + facnu + facnu*nolfm;				  
						
						//println(var_factor_t[facnu*(t-1):facnu*t-1][]);
						Q_t [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1]
						    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1] = var_factor_t[facnu*(t-1):facnu*t-1][]*(omt_f[t-1].^(-1/2));
						//////Q_t [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1]
						//////    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1] = var_factor_t[t-1];
						
						F1_t[0:2*facnu+(2*facnu)*nolfq-1]
						    [0:2*facnu+(2*facnu)*nolfq-1] 						        = unit(nolfq+1)**unit(2*facnu);		   //quarterly flow
						F1_t[2*facnu+(2*facnu)*nolfq: 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq - 1]
						    [2*facnu+(2*facnu)*nolfq: 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq - 1]	= unit(nolsq+1)**unit(1*facnu);		   //quarterly stock
						F1_t[2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq:]
						    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq:]  	   			= unit(nolfm+1)**unit(facnu);		   //monthly
						
						
						//////for (decl k = 0; k<lagof;k++)
						//////	{
						//////		F1_t[2*facnu + facnu*k:3*facnu-1 + facnu*k][2*facnu + facnu*k :3*facnu-1 + facnu*k] 	= unit(facnu);	
						//////	}
						
						if(nolfq > 0)
						{
						F2_t[2*facnu: 2*facnu+(2*facnu)*nolfq-1]
						    [0      : (2*facnu)*nolfq-1] 			= unit(nolfq)**unit(2*facnu);
						
						}
						
						//////if(nolsq > 0)
						//////{
						//////F2_t[2*facnu: 2*facnu+(2*facnu)*nolfq-1]
						//////    [0      : (2*facnu)*nolfq-1] 			= unit(nolfq)**unit(2*facnu);
						//////
						//////}
						
						F1_t[0:2*facnu-1] 				[dimf-facnu-facnu*nolfm : dimf-1-facnu*nolfm] 	= W_t_kq_f;
						F1_t[2*facnu:2*facnu+1*facnu-1] [dimf-facnu-facnu*nolfm : dimf-1-facnu*nolfm] 	= W_t_kq_s;
						
						F2_t[0:2*facnu-1] [0:2*facnu-1] 	   							= I_t_kq_f;
						F2_t[2*facnu:2*facnu+1*facnu-1] [2*facnu:2*facnu+1*facnu-1] 	   				= I_t_kq_s;
						
						
						//decl lagof_c = max(lagof-1,nolfm);
						
						if(nolfm == 0){
						F2_t[2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1]
						    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1] = mPhim;
							  		  }
									  
						else if(nolfm > 0){
						F2_t[2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu-1]
						    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu -1 + facnu*(lagof-1)] 	= mPhim;
						F2_t[2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu  : 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + facnu + (nolfm)*facnu -1]
						    [2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq 		: 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + (nolfm)*facnu -1] 			= unit(nolfm)**unit(facnu);
						//	//println(" unit(lagof_c)**unit(facnu) ", unit(lagof_c)**unit(facnu));						  
						//	//println(" lagof_c lagof nolf", lagof_c,  lagof, nolfm);
							  		 }
						//println(" F1_t :", F1_t);
						//println(" F2_t :", F2_t);
						
						decl inv_F1_t = invert(F1_t);
								  F_t = inv_F1_t*F2_t;
						          Q_t = inv_F1_t*Q_t*inv_F1_t';
}
	 if(returnval == 1){   return {F_t     , Q_t       };   }
else if(returnval == 2){   return {W_t_kq_f, I_t_kq_f, W_t_kq_s, I_t_kq_s};   }
}													  
/****************CONSTRUCTING COEFFICIENTS MATRICES******************************************************************/





/****************CALC_VARS***************************************************************************************************/
CALC_VARS(const yy, const full_mBtTm, const Sigma2y_dof_, const Sigma2y_Scale_,const n_qfs_, const l, const mlambdam)
{
					
					//println(" BC ", BC);
					decl VARS = .NaN*zeros(n_qfs_, 1);
					decl err  = .NaN*zeros(n_qfs_, dSampleT);
					
					decl bas, bit;
					
						if(l==1){bas = 1;
							   	 bit = n_qfs1+1;
								}
					////println( " bas ", bas,  " bit ", bit);
					decl out_meas = CONSTRUCT_MEAS(vlambdam_rgdp, mlambdam);
					decl H1 	  = out_meas[0]; 
					
					decl H;
					decl out_H = CONSTRUCT_MEAS_TIME(H1, vlambdam_rgdp);
					
						
						for(decl i = 0; i < dSampleT; i++)
						{
						if (n_qfs>0)
							{
							  //H = out_H[vecindex(month_t[i][].== 1)];
								H = out_H[1];
							}
					else	{	H = H1;   }
					
					
					////println(" yy[bas:bit-1][] ", (yy[bas:bit-1][] )');
					
					for(decl k = bas; k < bit; k++)  
								{	if (yy[k][i] == mMVAL)
										{	err[k-bas][i] = mMVAL; }	// if				  
									else
										{	err[k-bas][i] = yy[k][i] - H[k][]*(full_mBtTm)'[][i];	} // else 	 
								} // for k
						} // for i
					
					
						for(decl kk = 0; kk < n_qfs_; kk++)
							{   decl vWt 		= 1 - (err[kk][] .== mMVAL);
								decl res = err[kk][vecindex(vWt)]';	               //println(" kk ", kk, " res ",res);
								VARS[kk] = SAMPLE_SIGMAY(res, Sigma2y_dof_, Sigma2y_Scale_, kk);
							} // for kk
//			//println(" VARS ", VARS);
return VARS;
}
/****************CALC_VARS*******************************************************************************************/







/****************KALMAN FİLTER***************************************************************************************/
KALMAN_FILTER(vlambdam_rgdp_, mPhim_, const var_factor_t, const yy_star, const returnval, var_gdp_t, const omt_f, const mlambdam)
{
								decl nos    = dimf;
								decl tstar  = sizec(yy_star);	 		        ////println("tstar  :", tstar);
								decl Bttm   = zeros(nos,tstar);
								
								decl factor_qf = zeros(2*facnu,tstar);		 // facnu*(quarterly f-s, monthly f-s, weekly f-s, daily = 7)
								decl factor_m  = zeros(1*facnu,tstar);
								decl Pttm      = zeros(nos,tstar*nos);
								decl mKtt      = zeros(nos,tstar*nov);
								
								/*Initialize Kalman Filter */
								decl Btt       = zeros((2*facnu) + (1*facnu) +facnu*lagof, 1);		 
								decl Ptt       = 0;
								//decl t_vr  = invert(unit(dim^2)-F**F)*vec(Q);
								//decl Ptt   = shape(t_vr , dim, dim);
								
								decl l_like  = 0;
								decl l_like_rgdp  	= 0;
								
								decl i, K;
								
								decl out_meas = CONSTRUCT_MEAS(vlambdam_rgdp_, mlambdam);
								decl H1 	= out_meas[0]; 
								decl R 		= out_meas[1];
								
								decl H;
								decl out_H = CONSTRUCT_MEAS_TIME(H1, vlambdam_rgdp_);
								
								for (i=0; i<tstar; i++)
								{
								
									if (n_qfs>0)
										{
												//H = out_H[vecindex(month_t[i][].== 1)];
												H = out_H[1];
										}
									else	{	H = H1;   }
								
									if(SV_gdp==1)
									{	R[0][0] = var_gdp_t[i];   }
								
								
									if(SV_m==1)
									for(decl nm=0; nm<n_m; nm++)
									{	R[n_qfh + n_qfs1 + nm][n_qfh + n_qfs1 + nm] = var_m_t[i][nm];	  }
								
									
									decl out = CONSTRUCT_COEF(i, mPhim_, var_factor_t, 1, omt_f);
									decl F_t = out[0]; 
									decl Q_t = out[1];
									
									decl vWt 		= 1-(yy_star[][i] .== mMVAL);     // if(i==0){//println(yy_star[][i]);}
									decl Wt 		= diag(vWt); 						// //println(Wt);
									decl ystarmiss  = Wt*yy_star[][i];
									decl mRmiss		= Wt*R*Wt';
									decl mHmiss 	= Wt*H;   //println(mHmiss);
										
								    /*===================KALMAN FILTER=============================*/
								    decl vBttlag 	= F_t * Btt ;	      			          //println(mHmiss);     //predict: vBttlag=B_{t|t-1}  Btt=B_{t-1|t-1}  F=F
								    decl mPttlag 	= F_t * Ptt * F_t' + Q_t;			      //predict: mPttlag=P_{t|t-1}  Ptt=P_{t-1|t-1}  Q=Q
								
									decl eta    	= ystarmiss - mHmiss * vBttlag;	          //println(mHmiss);   //predict:
								     decl f      	= mHmiss * mPttlag * mHmiss' + mRmiss;	  //predict: f=f_{t|t-1}  R=R
								    decl invf   	= invertgen(f,3);
										 K      	= mPttlag * mHmiss'*invf;		          //println(K); //K=Kalman Gain K	  
								         Btt 		= vBttlag + K * eta;				      //update:	 B_{t|t} = K*\eta_{t}
								         Ptt 		= (unit(nos) - K * mHmiss ) * mPttlag;	  //update:	 P_{t|t} = (I-K*H)*P_{t|t-1}
								        /*=============================================================*/			 
										Bttm[][i]                 = Btt;		 
								        Pttm[][i*nos:(i+1)*nos-1] = Ptt;
										mKtt[][i*nov:(i+1)*nov-1] = K;			 
								
										if ((i > 3)&&(i<tstar-3))
										 {
										 	decl nonmis  = sumc(vWt);
										 	decl fnonmis =  f[vecindex(vWt)][vecindex(vWt)];	         ////println(f); //println(fnonmis);
										 	decl sign;		 decl logdetf = logdet(fnonmis, &sign);		
										 	l_like  = l_like + -0.5*nonmis*log(M_2PI) - 0.5*logdetf - 0.5*(eta'*invf*eta);			 //  //println(" l_like ", l_like);
								
										  decl rgdp_mis  = vWt[0];
								
													if(rgdp_mis==1)
													{	decl fnonmis =  f[0][0];	         ////println(f); //println(fnonmis);
											 			decl sign;		 decl logdetf = logdet(fnonmis, &sign);		
											 			l_like_rgdp  = l_like_rgdp + -0.5*1*log(M_2PI)-0.5*logdetf-0.5*(eta[0]'*invf[0][0] *eta[0]);
													}   // else
								
												else{	l_like_rgdp = l_like_rgdp + 0;	 }
											}	
								}
					   
	 if(returnval == 1){   return l_like_rgdp;   }
else if(returnval == 2){   return l_like;		 }
}
/****************KALMAN FİLTER***************************************************************************************/








/****************SAMPLE_LAMBDA_VOL_NoSurvey***************************************************************************************/
SAMPLE_LAMBDA_VOL_NoSurvey(const vparhat_, const mparvar_, const Sigma2y_dof_, const Sigma2y_Scale_, const yy_star, const X, const index_l, var_gdp_t, const index_pr)
{
	decl var_gdp1t, var_m1t;

	decl mX = X[][facnu*(index_l-1) : facnu*(index_l)-1];   // factor array
	decl mY = yy_star';	 				//println(mY);
	
	mX 		  = mX[Start_t0:][];		//println(Start_t0);
	mY	  	  =	mY[Start_t0:][];		//println(" (mX) ", mX); 
//     println("no_vec", no_vec);
	decl no 	  = no_vec[index_l];    // println("no_vec ", no_vec, " index_l ", index_l," no ",no);	
	decl mlambda  =	.NaN*zeros(no,facnu);
	decl vSigmay  = .NaN*zeros(no,1);
	decl std_fact = .NaN*zeros(no,facnu);
//	 println("here");
	decl  mparvar, vparhat;
	for (decl j=sumr(no_vec[:index_l-1]); j<sumr(no_vec[:index_l]); j++)
		{	//println(j);
			
					decl vWt  = 1-(mY[][j] .== mMVAL);   ////println(Wt);	   		
					decl vind =	vecindex(vWt);
					decl TT   = rows(vind);
					decl vYi  = mY[vind][j];	   	// //println(" vind ", vind);
				
					decl mXi  = mX[vind][];		// if(j==0){//println(" vYi ", vYi~mXi, " mXi ");}
			
					if ( (index_l==1) && (SV_gdp==1) )
					{	var_gdp1t = var_gdp_t[vind];	}
			
					if ( (index_l==3) && (SV_m==1) )
					{	var_m1t = var_m_t[vind][j-sumr(no_vec[:index_l-1])];	}
			
					std_fact[j-sumr(no_vec[:index_l-1])][] = moments(mXi,2)[2][];
					
					decl vari      = vVarym[j];
					decl i, vpar;
					decl rvYi      = vYi;  ////println(psi_i');/*- mXi[][0]*mlambda[j][0]*/;
					decl rmXi      = mXi; 
					decl rmparvar_ = mparvar_;
				    decl rvparhat_ = vparhat_;
							
					if ( (index_l==3) && (SV_m==1) )
					{
						decl CHOLINVOMEGA = zeros(TT*facnu, TT*facnu);
						decl jt;
							for	(jt=lagof; jt<TT; jt++)
							{
						 		decl Qt;
					//			if(t_distr_gdp == 1)
					//			{Qt      = diag(var_gdp1t[jt])/omt_gdp[jt];}
					//			else
					//			{
								Qt      = diag(var_m1t[jt]);
					//			}
								CHOLINVOMEGA[jt*facnu:(jt+1)*facnu-1][jt*facnu:(jt+1)*facnu-1] = choleski(invertsym(Qt));	//	  //println("choleski(invertsym(Qt))", choleski(invertsym(Qt)));
							}
						decl vecy    = vec(rvYi');
						 	 vecy    = CHOLINVOMEGA'*vecy;
							 vecy    = vecy[:sizer(vecy)-1][];
						decl x_tilde = rmXi**unit(facnu);
						 	 x_tilde = CHOLINVOMEGA'*x_tilde;
							 x_tilde = x_tilde[:sizer(vecy)-1][];
					
						mparvar = invertsym(invertsym(rmparvar_)            +  x_tilde'x_tilde);	  ////println(vari, " ",rmXi);  //common factor un variance'i 1 olarak assume edildi
						vparhat = mparvar *(invertsym(rmparvar_)*rvparhat_  +  x_tilde'vecy);
						vpar    = vparhat + CHOLBack(mparvar)*rann(1,1);
					
						mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';
						decl res = vYi - mXi*(mlambda[j-sumr(no_vec[:index_l-1])][]');	 		// //println(varc(vYi));	 
					
						decl out = SVdrawm(res, vh_m, vh_m_frcst, XtT0SV_m, PtT0SV_m, sqrt(dSigSV_m), dPhiSV_m, dMuSV_m, 0, hrzn, vind, vSigmay_vl_m, mmnt);		//println( " vind ",vind);
						vh_m				= out[0];
						XtT0SV_m			= out[1];
						PtT0SV_m			= out[2];
						dSigSV_m 			= sqr(out[3]);
						dMuSV_m 			= out[4];
						dPhiSV_m 			= out[5];
						vSigmay_vl_m	  	= out[6];
					//	vh_frcst	= out[7];
					//	mmnt		= out[8];
					//	println(" dSigSV ", dSigSV);
					/***********************************************************************************************************************/
					
						decl ind_m_cont =	zeros(frcst,1);
						decl vh_m_nwcst = 	zeros(frcst,1);
						decl h_temp = vh_m[rows(vh_m)-1];
			
						for(decl kk = 0; kk<frcst; kk++)
						{
							if(kk==0){ ind_m_cont[kk] = vind[rows(vind)-1]+1;} 
							else     { ind_m_cont[kk] = ind_m_cont[kk-1]+1;    }
						
							h_temp = dMuSV_m + dPhiSV_m*h_temp + rann(1,1)*sqrt(dSigSV_m);
							vh_m_nwcst[kk] = h_temp;
						}
						var_m_t[vind|ind_m_cont][j-sumr(no_vec[:index_l-1])] = exp(vh_m|vh_m_nwcst);
						/***********************************************************************************************************************/	
					} // if
					
			
					if ( (index_l==1) && (SV_gdp==1) )
					{
						decl CHOLINVOMEGA = zeros(TT*facnu, TT*facnu);
						decl jt;
							for	(jt=lagof; jt<TT; jt++)
							{
						 		decl Qt;
					//			if(t_distr_gdp == 1)
					//			{Qt      = diag(var_gdp1t[jt])/omt_gdp[jt];}
					//			else
					//			{
								Qt      = diag(var_gdp1t[jt]);
					//			}
								CHOLINVOMEGA[jt*facnu:(jt+1)*facnu-1][jt*facnu:(jt+1)*facnu-1] = choleski(invertsym(Qt));	//	  //println("choleski(invertsym(Qt))", choleski(invertsym(Qt)));
							}
						decl vecy    = vec(rvYi');
						 	 vecy    = CHOLINVOMEGA'*vecy;		  //println(sizer(vecy));
						decl x_tilde = rmXi**unit(facnu);
						 	 x_tilde = CHOLINVOMEGA'*x_tilde;	  //println(sizer(x_tilde));							 

							 decl dropTtemp; 
							 if(sizer(vecy) >= 205 && sizer(vecy) <= 212 )
							 {
							 	dropTtemp = range(205,sizer(vecy),1)';
							     vecy     = dropr(vecy, dropTtemp); 		  //202 implies data until 2020
								 x_tilde  = dropr(x_tilde, dropTtemp);
							 }	 
							 
						mparvar = invertsym(invertsym(rmparvar_)            +  x_tilde'x_tilde);	  ////println(vari, " ",rmXi);  //common factor un variance'i 1 olarak assume edildi
						vparhat = mparvar *(invertsym(rmparvar_)*rvparhat_  +  x_tilde'vecy);

//						if(data_name[selection[j]] == "_5" || data_name[selection[j]] == "_6l1" )
//						{
//		 					decl ua = 0;	 decl ub = probn(( 0 -vparhat)/sqrt(mparvar));	  decl uc = ua+(ub-ua)*ranu(1,1);
//							decl vpar = vparhat + CHOLBack(mparvar)*quann(uc);
//		 					mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';
//						}
//
//
//						else 
//						{
//		 					decl ua = probn(( 0 -vparhat)/sqrt(mparvar));	 decl ub = 1;	  decl uc = ua+(ub-ua)*ranu(1,1);
//							decl vpar = vparhat + CHOLBack(mparvar)*quann(uc);
//		 					mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';
//						}
//
//						if(mlambda[j-sumr(no_vec[:index_l-1])][] == .NaN || mlambda[j-sumr(no_vec[:index_l-1])][] == +.Inf || mlambda[j-sumr(no_vec[:index_l-1])][] == -.Inf)
//						{
//						decl vpar    = vparhat + CHOLBack(mparvar)*rann(facnu,1);	
//						mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';
//						}
//						println(" j ", j, "vpar ", mlambda[j-sumr(no_vec[:index_l-1])][]);

						decl vpar    = vparhat + CHOLBack(mparvar)*rann(facnu,1);	
						mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';		//println(vpar);
//						mlambda[j-sumr(no_vec[:index_l-1])][] = 1;		//println(vpar);

//						if(data_name[selection[j]] == "_6l1" )
//						{ if(mlambda[j-sumr(no_vec[:index_l-1])][] >0) {mlambda[j-sumr(no_vec[:index_l-1])][] = 0;}}


						decl res = vYi - mXi*(mlambda[j-sumr(no_vec[:index_l-1])][]');	 		// //println(varc(vYi));	 
					
							res_gdp 			= res;
						decl res_gdp_sq 		= res_gdp.^2;
						decl log_res_gdp_sq 	= log(res_gdp_sq);
					
						decl rows_my = rows(mY);
							if ( (mY[rows(mY)-1][0]==mMVAL)&&( mY[rows(mY)-2][0]==mMVAL ) )
							{vind = vind|(vind[rows(vind)-1]+3);}
					//		println( " vind ",vind);
					
														 //println(vh_gdp_frcst);
						decl out = SVdrawm(res, vh_gdp, vh_gdp_frcst, XtT0SV, PtT0SV, sqrt(dSigSV), dPhiSV, dMuSV, 0, hrzn, vind, vSigmay_vl, mmnt);//	println( " vind ",vind);
						vh_gdp		= out[0];
						XtT0SV		= out[1];
						PtT0SV		= out[2];
						dSigSV 		= sqr(out[3]);	  //	println(" dSigSV ", dSigSV);
						dMuSV 		= out[4];
						dPhiSV 		= out[5];
						vSigmay_vl  = out[6];
						//	vh_frcst	= out[7];
						//	mmnt		= out[8];
					
						/***********************************************************************************************************************/	
						decl ind_cont =	zeros(hrzn,1);
						decl vh_nwcst = zeros(hrzn,1);
						decl h_temp = vh_gdp[rows(vh_gdp)-1];
					
						for(decl kk = 0; kk<hrzn; kk++)
						{
							if(kk==0){ ind_cont[kk] = vind[rows(vind)-1]+3;} 
							else     { ind_cont[kk] = ind_cont[kk-1]+3;    }
						
							h_temp = dMuSV + dPhiSV*h_temp + rann(1,1)*sqrt(dSigSV);
							vh_nwcst[kk] = h_temp;
						}
						//println(vind,ind_cont);
			
//						if ( (mY[rows(mY)-1][0]==mMVAL)&&( mY[rows(mY)-2][0]==mMVAL ) )
//						{var_gdp_t[vind|ind_cont[:rows(ind_cont)-2]] = exp(vh_gdp|vh_nwcst);}
//					
//  				    	else 	{var_gdp_t[vind|ind_cont] = exp(vh_gdp|vh_nwcst);}
//						var_gdp_t[vind|ind_cont] = exp(vh_gdp|vh_nwcst);
						var_gdp_t[index_pr] = exp(vh_gdp|vh_nwcst);
					
						ht_gdp	  = vh_gdp;
						ht_gdpT	  = vh_nwcst;
					/***********************************************************************************************************************/	
					} // if
					
					else
					{
			
						mparvar = invertsym(invertsym(rmparvar_)            +  vari^(-1)*rmXi'*rmXi);	  ////println(vari, " ",rmXi);  //common factor un variance'i 1 olarak assume edildi
						vparhat = mparvar *(invertsym(rmparvar_)*rvparhat_  +  vari^(-1)*rmXi'*rvYi);
						vpar    = vparhat + CHOLBack(mparvar)*rann(facnu,1);
					
						mlambda[j-sumr(no_vec[:index_l-1])][] = vpar';
						decl res = vYi - mXi*(mlambda[j-sumr(no_vec[:index_l-1])][]');	 		// //println(varc(vYi));	 
						vSigmay[j-sumr(no_vec[:index_l-1])] = SAMPLE_SIGMAY(res, Sigma2y_dof_, Sigma2y_Scale_, j-sumr(no_vec[:index_l-1]));					 // if(j==0){//println(" vYi ", mXi*(mlambda[j-sumr(no_vec[:index_l-1])][]'), " mXi ");}		  
						//	if ( (index_l==1) )
						//	{vSigmay[j-sumr(no_vec[:index_l-1])] = 2;}
				} // else
	
	} // for (decl j=sumr(no_vec[:index_l-1]); j<sumr(no_vec[:index_l]); j++)

return {mlambda, vSigmay, mlambda.*std_fact, res_gdp, ht_gdp, ht_gdpT, var_gdp_t};
}
/****************SAMPLE_LAMBDA_VOL_NoSurvey***************************************************************************************/









/**************** SAMPLE_FAC_VAR***************************************************************************************/
SAMPLE_FAC_VAR(const dof_, const scale_, const frcst, const mBtTm_frcst, const var_fac_t)
{
		decl mVar;		decl tstar = sizer(mBtTm[][]);	 decl omt_f = nans(tstar,1);
		if (SV_fac == 1)
			{

				/**********************************************************/
				decl vfsv     = mBtTm[][facnu*(3-1):facnu*3-1];											   //println(" vfsv ",vfsv);
				decl t_sv     = rows(vfsv);
//				decl vfxsv	  = zeros(t_sv,facnu*lagof);														   //println(" vfxsv ",vfxsv);
				decl  vfxsv	  = lag0(vfsv,(range(1,lagof,1)'));
				vfxsv[0][]    =	vfxsv[1][];
				decl ystarsv  = vfsv [][];								
				decl xstarsv  = vfxsv[][];	  	  
				decl res_sv   = ystarsv - xstarsv*mPhim';													//println( " rows(res_sv) ", rows(res_sv));
		 		/**********************************************************/

                /***********************Draw t ****************************/
				for(decl t=0; t<tstar; t++)
				{	
				omt_f[t][]  = rangamma(1, 1, (doft_f + 1)/2, (  doft_f + ( sqr(res_sv[t])./var_fac_t[t] )  )/2  );
		 		res_sv[t][] = (omt_f[t].^(1/2) ).*res_sv[t][];
				}
				/***********************Draw t ****************************/

				
				decl vind    = 0;
				decl out     = SVdrawm(res_sv, vh_f, vh_f_frcst, XtT0SV_f, PtT0SV_f, sqrt(dSigSV_f), dPhiSV_f, dMuSV_f, 0, hrzn, vind, vSigmay_vl_f, mmnt);
				vh_f 		 = out[0];
				XtT0SV_f	 = out[1];
				PtT0SV_f	 = out[2];
				dSigSV_f 	 = sqr(out[3]);
				dMuSV_f 	 = out[4];
				dPhiSV_f 	 = out[5];
				vSigmay_vl_f  = out[6];
	
				decl vh_f_frcst = zeros(frcst,1);
				decl h_temp     = vh_f[rows(vh_f)-1];
				for(decl k = 0; k<frcst; k++)
					{
						h_temp = dMuSV + dPhiSV*h_temp + rann(1,1)*sqrt(dSigSV_f);		//	println(dMuSV, " ", dPhiSV);
//						h_temp =  h_temp + rann(1,1)*sqrt(dSigSV_f);
						vh_f_frcst[k] = h_temp;	
					}  //	println(ind_cont ~ vh_frcst ~ exp(vh_frcst));

				mVar = exp(vh_f|vh_f_frcst);
			}
		else
			{
				/**********************************************************/
				decl rows_fac = rows(mBtTm);
				decl vf    	  = mBtTm[:rows_fac-4][facnu*(3-1):facnu*3-1]| mBtTm_frcst[][facnu*(3-1):facnu*3-1];   //		 //println(" vf ",vf);
				decl t_       = rows(vf);		 //println(" t_ ", t_)	 ;
				decl vfx	  = zeros(t_,facnu*lagof);
			 		 vfx   	  = lag0(vf,(range(1,lagof,1)'));
				decl ystar 	  = vf [][];								
				decl xstar 	  = vfx[][];	  	  																			 //		println(" vfx ",vfx);
				decl res      = ystar - xstar*mPhim';
				/**********************************************************/
		
				decl SCALE 	  = res'res + scale_;
				decl novI  	  = columns(res);
				decl DoF   	  = rows(res) + dof_;					 ////println(dof_);
				decl mL       = CHOLBack(SCALE)';
		
			  	mVar  	= mL'*( diag(ranchi(novI,1,DoF).^(-1)) )*mL;
				mVar    = ones(rows(vf)+3,1)**mVar;   //	   println( " mVar " , mVar);
			}

			omt_f = omt_f|ones(frcst,1);

return {mVar, omt_f};
}
/****************SAMPLE_FAC_VAR***************************************************************************************/







/****************SAMPLE_PHII***************************************************************************************/
SAMPLE_PHII(const phihat_, const phivar_, const vBtT0m, var_1, const omt_f)
{
	decl rows_fac 	= rows(mBtTm);
	decl vf    		= mBtTm[:rows_fac-4][facnu*(3-1):facnu*3-1];
	decl t_	   		= sizer(vf);	  //println( " t_ " ,t_);

	decl vfx 	= zeros(t_, facnu*lagof);
		 vfx 	= lag0(vf, (range(1,lagof,1)'));

	decl ystar  = vf [lagof:][];								
	decl xstar  = vfx[lagof:][];

	decl CHOLINVOMEGA = zeros((t_-lagof)*facnu, (t_-lagof)*facnu);
	decl jt;
	for	(jt=lagof; jt<t_; jt++)
		{
		//	 		decl Qt      = diag(var_1[jt]);			var_factor_t[facnu*(t-1):facnu*t-1][]
					decl Qt      = var_1[facnu*(jt-1):facnu*jt-1][]*(omt_f[jt-1].^(-1/2)); ;	//println(Qt)	 ;

					CHOLINVOMEGA[(jt-lagof)*facnu:((jt-lagof)+1)*facnu-1][(jt-lagof)*facnu:((jt-lagof)+1)*facnu-1] = choleski(invertsym(Qt));	//	 //println("choleski(invertsym(Qt))", choleski(invertsym(Qt)));
		}

	decl vecy    = vec(ystar');
		 vecy    = CHOLINVOMEGA'*vecy;

	decl x_tilde = xstar**unit(facnu);
		 x_tilde = CHOLINVOMEGA'*x_tilde;

	decl phivar = invertsym(invertsym(phivar_)         +  x_tilde'x_tilde);	   
	decl phihat = phivar  *(invertsym(phivar_)*phihat_ +  x_tilde'vecy);

	decl vPhi    = phihat + choleski(phivar)*rann(facnu*facnu*lagof,1);
		 vPhi	= reshape(vPhi,facnu*lagof, facnu)';

///* Acceptence Rejection */
//decl vPhi,i;   decl Philb = 0.0;
// decl accept=0;
// 	for(i=0; accept!=1; i++)					 
//	{
//    decl  ua   = probn(( Philb -phihat)/sqrt(phivar));
//    decl  ub   = probn(( 1.0     -phihat)/sqrt(phivar));
//    decl  uc   = ua+(ub-ua)*ranu(1,1);
//    vPhi       = phihat+sqrt(phivar)*quann(uc);
//
//////	vPhi = phihat + choleski(phivar)*rann(facnu*facnu*lagof,1);
////	decl COEF =	(1|(-vPhi[]));
////	decl roots; polyroots(COEF', &roots);
////	decl rootmod = sqrt(sumsqrc(roots));
////	if (max(rootmod) > 0.99)  // { println("vPhi ", vPhi) }
////    {println("---------------------------PHI Unit Root-----------------------------------");	 continue;}
//   if(vPhi ==  .NaN)  {vPhi = Philb; println(vPhi);}
//   if(vPhi == +.Inf)  {vPhi = Philb; println(vPhi);}
//   
//	 accept=1;
//	}
/* Acceptence Rejection */
//println("vPhi ", phi);

return {vPhi, phihat, phivar};		
}
/****************SAMPLE_PHII***************************************************************************************/







/****************SAMPLE_PHI_MH***************************************************************************************/
SAMPLE_PHI_MH(const phihat_, const phivar_, const vBtT0m, vPhi_old, const yy_star, MHphi_acc_, const var_gdp_t, const var_factor_t, const omt_f, const mlambdam)
{
vPhi_old = vecr(vPhi_old);
decl vPhi_star, vPhihat_cand, vPhivar_cand;
decl out		  = SAMPLE_PHII(phihat_, phivar_, vBtT0m, var_factor_t, omt_f);
	vPhi_star     = out[0];
	vPhi_star = vecr(vPhi_star);
	
	vPhihat_cand  = out[1];
	vPhivar_cand  = out[2];

    decl i;
//    decl vQ_old   = log( (1/vPhistd_cand^(0.5)) *densn((vPhi_old  - vPhihat_cand)/vPhistd_cand^(0.5)) );
//    decl vQ_old  = log(                   1/sqrt(M_2PI*vPhistd_cand)                     *              exp(-0.5*         ((vPhi_old - vPhihat_cand)/vPhistd_cand)          		)                                       );
//	decl vQ_old  = log( (1/(sqrt(M_2PI*vPhistd_cand^2)) * exp(-0.5*	(vPhi_old - vPhihat_cand)/vPhistd_cand)^2	) );
	decl vQ_old  = log(                determinant(M_2PI*vPhivar_cand)^(-0.5)                       *              exp(-0.5*       (vPhi_old  - vPhihat_cand)' * invert(vPhivar_cand) * (vPhi_old  - vPhihat_cand)          		) 	                                        );

	decl vP_old;
  	vP_old = KALMAN_FILTER(vlambdam_rgdp, vPhi_old, var_factor_t, yy_star, 2, var_gdp_t, omt_f, mlambdam); 
  
//  decl vQ_new   	= log( (1/vPhistd_cand^(0.5)) *densn((vPhi_star - vPhihat_cand)/vPhistd_cand^(0.5)) );
  	decl vQ_new  	= log(                determinant(M_2PI*vPhivar_cand)^(-0.5)                       *              exp(-0.5*       (vPhi_star  - vPhihat_cand)' * invert(vPhivar_cand) * (vPhi_star  - vPhihat_cand)          		) 	                                        );

  	decl vPhi_new 	= vPhi_star;
  	decl vP_new   	= KALMAN_FILTER(vlambdam_rgdp, vPhi_new, var_factor_t, yy_star, 2, var_gdp_t, omt_f, mlambdam);

  	decl MHratio    = min(1, exp((vP_new + vQ_old) - (vP_old + vQ_new)) );
  		 MHphi_acc_ = MHphi_acc_|MHratio;
//
if(	printorder_mh == 1)
{
  println(" vPhi meanc(MHphi_acc) " , meanc(MHphi_acc));
  println(" vPhi MHratio : ", MHratio);
}
  if(ranu(1,1) < MHratio){ vPhi_old = vPhi_new; }
  else 		          	 { vPhi_old = vPhi_old; }

decl vPhi = vPhi_old;
	 vPhi	= reshape(vPhi,facnu*lagof, facnu)';

//println(" vPhi: ", vPhi);
return {vPhi, MHphi_acc_};	
}
/****************SAMPLE_PHI_MH***************************************************************************************/






/****************SAMPLE_BtT***************************************************************************************/
SAMPLE_BtT(BtT0, PtT0, yy_star, frcst, const  now_index, const var_gdp_t, const var_factor_t, const omt_f, const mlambdam)
{
					decl nos    = dimf;
				
					decl yy_star_    = yy_star~( mMVAL* ones(nov, frcst) ) ;	   
					decl tstar       = sizec(yy_star_);	 		       ////println("tstar  :", yy_star');
					decl Bttm        = zeros(nos,tstar);
					
					decl factor_qf   = zeros(2*facnu,tstar);		 // facnu*(quarterly f-s, monthly f-s, weekly f-s, daily = 7)
					decl factor_qs   = zeros(1*facnu,tstar);		 // facnu*(quarterly f-s, monthly f-s, weekly f-s, daily = 7)
					decl factor_m    = zeros(1*facnu,tstar);
					
					decl inf_ 		 =  zeros(tstar,1);
					decl R_   		 =  zeros(tstar,1);
					decl Pttm   	 = zeros(nos, tstar*nos);
					decl mKtt   	 = zeros(nos, tstar*nov);
					
					/*Initialize Kalman Filter */
					decl Btt       	 = BtT0;		    //println(Btt);     
					decl Ptt       	 = PtT0;
					
					decl l_like  	 = 0;
					decl l_like_rgdp = 0;
					decl l_like_ip   = 0;
					decl l_like_pr 	 = zeros(hrzn,1);
					decl inf_pr 	 = zeros(hrzn,1);
					decl y1t_sim 	 = zeros(hrzn,1);
					decl var_sim 	 = zeros(1,1);
					decl I 			 = zeros(hrzn,1);
					decl i, K;
					
					decl out_meas    = CONSTRUCT_MEAS(vlambdam_rgdp, mlambdam);
					decl H1 	     = out_meas[0]; 
					decl R 		     = out_meas[1];
					decl out_H       = CONSTRUCT_MEAS_TIME(H1, vlambdam_rgdp);
					decl H;
					
				
					/************************************************************************************************ Kalman filter ***************************************************************************************************************/
					for (i=0; i<tstar; i++)
					{
						if (n_qfs>0){   H = out_H[1]; }
						else		{	H = H1;   }
					
						if(SV_gdp==1)
						{   R[0][0] = var_gdp_t[i];	  }
					
						if(SV_m==1)
						for(decl nm=0; nm<n_m; nm++)
						{	R[n_qfh + n_qfs1 + nm][n_qfh + n_qfs1 + nm] = var_m_t[i][nm];	  }
					
						decl out = CONSTRUCT_COEF(i, mPhim, var_factor_t, 1, omt_f);
					//	println("---------------------------------------------------------");
						decl F_t = out[0]; 
						decl Q_t = out[1];
				
					/*************PREDICTIVE LIKELIHOOD CALCULATION***********************************************************************************/
						for(decl l = 0; l<hrzn; l++)
						{
							  if(i == now_index[l])
							  {  	
									decl yy_star_pr 	= yy_star_ [][i];
									yy_star_pr[0] 		= yy_gdp_stndrdzd[now_index[l]];					 	//println(yy_star_pr );
							//		if(i == now_index[0]) { println(" yy_star_pr[0] ", yy_star_pr[0]);}
									decl vWt_pr 		= 1-(yy_star_pr .== mMVAL);     //println(" now_index " ,now_index,"  i", i);			//println(" vWt ", vWt,  " sumc(vWt) ", sumc(vWt) );	// if(i==0){println(yy_star[][i]);}	  
								    decl Wt_pr 			= diag(vWt_pr); 						  		////println(" Wt ", Wt);
								    decl ystarmiss_pr   = Wt_pr*yy_star_pr;
								    decl mRmiss_pr		= Wt_pr*R*Wt_pr';
								    decl mHmiss_pr 		= Wt_pr*H;										//println(H);
							
									decl vBttlag_pr 	= F_t * Btt;	      			////println(mHmiss);     //predict: vBttlag=B_{t|t-1}  Btt=B_{t-1|t-1}  F=F
							        decl mPttlag_pr 	= F_t * Ptt * F_t' + Q_t;			              //predict: mPttlag=P_{t|t-1}  Ptt=P_{t-1|t-1}  Q=Q
									decl eta_pr    	= ystarmiss_pr - mHmiss_pr*vBttlag_pr;	                //println(" ystarmiss ", ystarmiss,  " mHmiss * vBttlag ", mHmiss * vBttlag);   //predict:
							        decl f_pr      	= mHmiss_pr * mPttlag_pr * mHmiss_pr' + mRmiss_pr;	         //println(mHmiss_pr, mPttlag_pr);	  //predict: f=f_{t|t-1}  R=R	
									decl invf_pr   	= invertgen(f_pr,3);
									
									decl fnonmis_pr =  f_pr[0][0];	         //println(f);//println(fnonmis);
									decl sign_pr;		 decl logdetf = logdet(fnonmis_pr, &sign_pr);		
							
									l_like_pr[l]  = -0.5*1*log(M_2PI)-0.5*logdetf-0.5*(eta_pr[0]'*invf_pr[0][0]*eta_pr[0]);	//println("%10.4f", " i ", i, ", f_pr[0][0] ", "%10.4f", f_pr[0][0]," invf_pr[0][0] ", "%10.4f", invf_pr[0][0]);        //println(" l ", l, " l_like_pr ",  l_like_pr[l]);
									inf_pr[l] 	  = invf_pr[0][0];
									l_like_pr[l]  = exp(l_like_pr[l]);
									y1t_sim[l]    = (mHmiss_pr*vBttlag_pr)[0] + rann(1,1)*sqrt(   mRmiss_pr[0][0]   );		 //println(" mRmiss_pr[0][0] ", mRmiss_pr[0][0]);
									I[l]		  = y1t_sim[l] < ystarmiss_pr[0];
							
									if(l==0){ var_sim =  mRmiss_pr[0][0]; }
						//		println(" I[l] ", I[l], " y1t_sim[l] ", y1t_sim[l], " ystarmiss_pr[0] ",ystarmiss_pr[0]);
							  }   // if(i == now_index[l])			//println(" yy_star_pr[0] ",yy_star_pr[0], " y1t_sim ",y1t_sim, " (mHmiss_pr*vBttlag_pr)[0] ", (mHmiss_pr*vBttlag_pr)[0], " sqrt(f_pr[0][0]) ", sqrt(f_pr[0][0]) );
				
						}   // for(decl l = 0; l<hrzn; l++)
					/*************PREDICTIVE LIKELIHOOD CALCULATION***********************************************************************************/
					
						decl vWt 		= 1-(yy_star_[][i] .== mMVAL);     	         //println(" vWt ", vWt,  " sumc(vWt) ", sumc(vWt) );	// if(i==0){println(yy_star[][i]);}	  
						decl Wt 		= diag(vWt); 						  		//println(" Wt ", Wt);
						decl ystarmiss  = Wt*yy_star_[][i];
						decl mRmiss		= Wt*R*Wt';
						decl mHmiss 	= Wt*H;										//println(H);
				
						if( sumc(vWt)>0 )
						{
							/*===================KALMAN FILTER=============================*/
					        decl vBttlag 	= F_t * Btt ;	      			//println(mHmiss);     //predict: vBttlag=B_{t|t-1}  Btt=B_{t-1|t-1}  F=F
					        decl mPttlag 	= F_t * Ptt * F_t' + Q_t;			              //predict: mPttlag=P_{t|t-1}  Ptt=P_{t-1|t-1}  Q=Q
					
							decl eta    	= ystarmiss - mHmiss * vBttlag;	                //println(" ystarmiss ", ystarmiss,  " mHmiss * vBttlag ", mHmiss * vBttlag);   //predict:
					        decl f      	= mHmiss * mPttlag * mHmiss' + mRmiss;		  //predict: f=f_{t|t-1}  R=R
							decl invf   	= invertgen(f,3);
							K      			= mPttlag * mHmiss'*invf;		             //println(" K ",K, " eta ",eta); //K=Kalman Gain K	  
					        Btt 			= vBttlag + K * eta;				                  //update:	 B_{t|t} = K*\eta_{t}
					        Ptt 			= (unit(nos) - K * mHmiss ) * mPttlag;	              //update:	 P_{t|t} = (I-K*H)*P_{t|t-1}
					      /*=============================================================*/			 
							inf_[i] = invf[0][0];
							
							if ( (i > 3) && (i<tstar) )
								 {
								 	decl nonmis  = sumc(vWt);    		//println( " nonmis ", nonmis);
							     	decl fnonmis =  f[vecindex(vWt)][vecindex(vWt)];	         //println(f);//println(fnonmis);
								 	decl sign;		 decl logdetf = logdet(fnonmis, &sign);		
								 	l_like  = l_like + -0.5*nonmis*log(M_2PI)-0.5*logdetf-0.5*(eta'*invf*eta);	  //println(" l_like ",l_like);
					
									decl rgdp_mis  = vWt[0];
									if(rgdp_mis==0)
										{
											l_like_rgdp  = l_like_rgdp + 0;
										}
									else
										{
											decl fnonmis =  f[0][0];	         //println(f);//println(fnonmis);
								 			decl sign;		 decl logdetf = logdet(fnonmis, &sign);
											
											R_[i]	= R[0][0];
								 			l_like_rgdp  = l_like_rgdp + -0.5*1*log(M_2PI)-0.5*logdetf-0.5*(eta[0]'*invf[0][0]*eta[0]);			 ////println(" i" ,i, " R[0][0] ", R[0][0], " invf[0][0] ",invf[0][0]);
										}   // else
								 }	  // ((i > 3)&&(i<tstar))			 
						}   //	if(sumc(vWt)>0)
				
					 		else
					 		{
				        		Btt = F_t * Btt;				                 
				        		Ptt = F_t * Ptt * F_t' + Q_t;
					 		}
				
						Bttm[][i]                 = Btt ;		//println(" Btt " ,Btt); 
				        Pttm[][i*nos:(i+1)*nos-1] = Ptt ;
				//		mKtt[][i*nov:(i+1)*nov-1] = K   ;			 
					}	//for (i=0; i<tstar; i++)
					/************************************************************************************************ Kalman filter ***************************************************************************************************************/
				
					/**************************************************************************************** Simulation Smoother Carter Kohn (1994) **********************************************************************************************/
				
					
					decl mBtt 		= Bttm;	      //println(" Bttm' ", Bttm');
					decl dStateStar = sizec(StateSel);
					//decl mBtT       = zeros(tstar,dStateStar);	  //The smoothed states
					decl mBtT       = Bttm[StateSel][]';
					decl BtT_tmp   	= Bttm[][ tstar-1                 ];
					decl PtT_tmp   	= Pttm[][(tstar-1)*nos:tstar*nos-1];
					//decl G                   = CHOLRobust(PtT_tmp[StateSel][StateSel], tres);
					decl G          = CHOLBack(PtT_tmp[StateSel][StateSel]);
					
					decl BtT        = BtT_tmp[StateSel][] + G*rann(dStateStar,1);
					mBtT[tstar-1][] = BtT';
					
					factor_m [][tstar-1]	= BtT;
				
					decl BtTfull;
					for (i=tstar-2; i>Start_t0-1; i--)
					{
						decl out = CONSTRUCT_COEF(i, mPhim, var_factor_t, 1, omt_f);
						decl F_t = out[0]; 
						decl Q_t = out[1];
					
							decl mFStar               = F_t[StateSel][];				                         //println(" mFStar ",mFStar);           //println(Bttm);
							decl etaTstar             = BtT - mFStar*Bttm[][i];		                             //print(" etaT   ",  etaTstar);
																								 
					   	    decl mQstar               = Q_t[StateSel][StateSel];		                         //println(" mQstar ",mQstar);
							decl   fT                 = mFStar*Pttm[][i*nos:(i+1)*nos-1]*mFStar' + mQstar;		 //println("Pttm[][i*nos:(i+1)*nos-1] ",Pttm[][i*nos:(i+1)*nos-1]);
							decl   KGainT             = Pttm[][i*nos:(i+1)*nos-1]*mFStar'*invertgen(fT,3);		 // print(" KGainT(fT,3)   ", KGainT," invertgen(fT,3) ",invertgen(fT,3));
						    Bttm[][i]                 = Bttm[][i] + KGainT*etaTstar;
						    Pttm[][i*nos:(i+1)*nos-1] = (unit(nos) - KGainT*mFStar)*Pttm[][i*nos : (i+1)*nos-1]; //println("Pttm[][i*nos:(i+1)*nos-1] ",Pttm[][i*nos:(i+1)*nos-1]);	  
					
					    	BtT_tmp     			 = Bttm[][i];
					    	PtT_tmp     			 = Pttm[][i*nos:(i+1)*nos-1];	                             //println("PtT_tmp ", PtT_tmp);	 //println("i ", i);
							BtTfull	                 = BtT_tmp;
					
							decl cholPtT_tmp;
							PtT_tmp = PtT_tmp[StateSel][StateSel];	   									//	println(" PtT_tmp ",PtT_tmp);	
					//		cholPtT_tmp = CHOLRobust(PtT_tmp, tres);						//	println(" cholPtT_tmp ",cholPtT_tmp);
							cholPtT_tmp 		 = CHOLBack(PtT_tmp);							//	println(" cholPtT_tmp ",cholPtT_tmp);
					
					//		println(" cholPtT_tmp ",cholPtT_tmp);
							BtTfull = BtT_tmp;
					    	BtTfull[StateSel]   = BtT_tmp[StateSel] + cholPtT_tmp*rann(dStateStar,1);
							BtT       			= BtTfull[StateSel];				  //println(XtT);
					
							factor_m  [][i]		= BtTfull[StateSel];
						}	 //loop i
				/* ??? */	
				//	factor_m = (standardize(factor_m'))';
				/* ??? */	
					factor_qf [][0]	= factor_m[][0];
					factor_qs [][0]	= factor_m[][0];
				
					/****************RECONSTRUCTING FACTOR BLOCKS  (from monthly to quarterly factor transformation)******************************************************************/
					for (decl i=1; i<tstar; i++)
					{
					decl out = CONSTRUCT_COEF(i, mPhim, var_factor_t, 2, omt_f);
					decl W_t_kq_f = out[0];			  ////println(" W_t_kq_f  --------------",W_t_kq_f);
					decl I_t_kq_f = out[1];
					
					decl W_t_kq_s = out[2];			  ////println(" W_t_kq_f  --------------",W_t_kq_f);
					decl I_t_kq_s = out[3];
					
					//println(I_t_kq_f, factor_qf[][i-1]);
					factor_qf [][i]	= -W_t_kq_f*factor_m[][i] + I_t_kq_f*factor_qf[][i-1];
					factor_qs [][i]	= -W_t_kq_s*factor_m[][i] + I_t_kq_s*factor_qs[][i-1];
					
					}
					//std_rt = moments((factor_qf[0][])')[2] / moments(factor_m')[2];
					//println(" std_rt ",std_rt);
				/* ??? */	
				//	  factor_qf = (standardize(factor_qf'))';
				//	  factor_qs = (standardize(factor_qs'))';
				/* ??? */
					/****************RECONSTRUCTING FACTOR BLOCKS  (from monthly to quarterly factor transformation)******************************************************************/
				
					decl frcst_factor_m  = .NaN*zeros(facnu  , frcst);
					decl frcst_factor_qf = .NaN*zeros(2*facnu, frcst);
					decl frcst_factor_qs = .NaN*zeros(2*facnu, frcst);
					
					frcst_factor_qf 	= factor_qf [][tstar-frcst:tstar-1];
					frcst_factor_qs 	= factor_qs [][tstar-frcst:tstar-1];
					frcst_factor_m  	= factor_m	[][tstar-frcst:tstar-1];	
					
					factor_qf 			= factor_qf [][:tstar-frcst-1];
					factor_qs 			= factor_qs [][:tstar-frcst-1];
					factor_m 			= factor_m  [][:tstar-frcst-1];
				//println(l_like_pr);

return {
        ((factor_qf[0:facnu-1][]')~(factor_qs[0:facnu-1][]')~(factor_m')),	 //	  	mBtTm
		((factor_qf'             )~(factor_qs'		       )~(factor_m')),	 //		full_mBtTm
		l_like,           BtT0,                 PtT0,               mBtt,                 mKtt,
		((frcst_factor_qf[0:facnu-1][]')~(frcst_factor_qs[0:facnu-1][]')~(frcst_factor_m')),
		((factor_qf'|frcst_factor_qf')	~	(factor_qs'|frcst_factor_qs')	~	(factor_m'|frcst_factor_m')),	//	full_mBtTm
		l_like_rgdp,     l_like_ip,             l_like_pr,          y1t_sim,              inf_                    , R_,        inf_pr             , I               , var_sim
	    };
}
/****************SAMPLE_BtT***************************************************************************************/








/**********************************NOWCASTING ALL VARIABLES************************************************************/
NOWCAST(const frcst, const yy_star, const full_mBtTm, const full_mBtTm_frcst, const now_index,const var_gdp_t, const mlambdam)
{
		decl yy_star_    = yy_star~( mMVAL* ones(nov, frcst) ) ;	   //println(yy_star_');
		decl tstar       = sizec(yy_star_);	 		       ////println("tstar  :", yy_star');
	
		decl yy_nowcast  = zeros(nov,tstar);
		decl yy_forecast = zeros(nov,tstar);
	
		decl out_meas 	 = CONSTRUCT_MEAS(vlambdam_rgdp, mlambdam);
		decl H1 		 = out_meas[0]; 
		//decl H2        = CONSTRUCT_MEAS_TIME(H1,i);
		decl R 			 = out_meas[1];
	
		decl H, out_H;
	
		for (decl i=0; i<tstar; i++)
			{
	
				if (n_qfs>0)
					{
	//					H = out_H[vecindex(month_t[i][].== 1)];
						out_H = CONSTRUCT_MEAS_TIME(H1, vlambdam_rgdp);
						H = out_H[1];
					}
				else	{	H = H1;   }
		
			  	decl mHmiss, mRmiss;
		
				if(SV_gdp==1)	  	 		                {   R[0][0] = var_gdp_t[i];	  }					 
				if(SV_m  ==1) for(decl nm=0; nm<n_m; nm++)  {	R[n_qfh + n_qfs1 + nm][n_qfh + n_qfs1 + nm] = var_m_t[i][nm];	  }
		
				yy_forecast[0][i] 	= (H[0][]*(full_mBtTm_frcst[i][]')) + rann(1,1)*sqrt( R[0][0] );	 // println(i," ", H[0][]'~(full_mBtTm_frcst[i][]'));
			}  // for (decl i=0; i<tstar; i++)

			
		return {yy_forecast, yy_forecast};
}
/**********************************NOWCASTING ALL VARIABLES********************************************************/



//
///**********************************NOWCASTING ALL VARIABLES************************************************************/
//NOWCAST(const frcst, const yy_star, const full_mBtTm, const full_mBtTm_frcst, const now_index,const var_gdp_t)
//{
//		decl yy_star_ = yy_star~( mMVAL* ones(nov, frcst) ) ;	   //println(yy_star_');
//		decl tstar    = sizec(yy_star_);	 		       ////println("tstar  :", yy_star');
//	
//		decl yy_nowcast  = zeros(nov,tstar);
//		decl yy_forecast = zeros(nov,tstar);
//	
//		decl out_meas 	= CONSTRUCT_MEAS(vlambdam_rgdp);
//		decl H1 		= out_meas[0]; 
//		//decl H2 = CONSTRUCT_MEAS_TIME(H1,i);
//		decl R 			= out_meas[1];
//	
//		decl H;
//		decl out_H = CONSTRUCT_MEAS_TIME(H1, vlambdam_rgdp);
//	
//	
//		for (decl i=0; i<tstar; i++)
//			{
//	
//			if (n_qfs>0)
//				{
//					H = out_H[vecindex(month_t[i][].== 1)];
//	//				H = out_H[1];
//				}
//			else	{	H = H1;   }
//	
//		  	decl mHmiss, mRmiss;
//	
//			if(SV_gdp==1)	  	 		                {   R[0][0] = var_gdp_t[i];	  }					 
//			if(SV_m==1)	  for(decl nm=0; nm<n_m; nm++)  {	R[n_qfh + n_qfs1 + nm][n_qfh + n_qfs1 + nm] = var_m_t[i][nm];	  }
//	
//			decl vWt= 1-(yy_star_[][i] .== mMVAL);     	    //	println(" vWt ", vWt,  " sumc(vWt) ", sumc(vWt) );	// if(i==0){println(yy_star[][i]);}	  
//			decl Wt = diag(vWt); 						 	////println(" Wt ", Wt);
//			mHmiss 	= Wt*H;
//			mRmiss	= Wt*R*Wt';
//			
//		  	for(decl l = 0; l<hrzn; l++)
//				{
//					if  (i == now_index[l]) 
//				  		{  	
//							decl yy_star_pr 	= yy_star_ [][i];
//							yy_star_pr[0] 		= yy_gdp_stndrdzd[now_index[l]];					 	//println(yy_star_pr );
//							decl vWt_pr 		= 1-(yy_star_pr .== mMVAL);     //	  	println(" now_index " ,now_index,"  i", i);			println(" vWt ", vWt,  " sumc(vWt) ", sumc(vWt) );	// if(i==0){println(yy_star[][i]);}	  
//					    	decl Wt_pr 			= diag(vWt_pr); 						  		////println(" Wt ", Wt);
//					        mHmiss 				= Wt_pr*H;
//							mRmiss				= Wt_pr*R*Wt_pr';
//						}
//	  			
//		  			if(i<tstar-frcst)						   //(mHmiss_pr*vBttlag_pr)[0] + rann(1,1)*sqrt(   mRmiss_pr[0][0]   )
//		  				{
//							yy_nowcast[0][i] 	= (mHmiss*full_mBtTm')[0][i] + rann(1,1)*sqrt( mRmiss[0][0] );
//							yy_forecast[0][i] 	= yy_nowcast[0][i];
//						}
//		  			else
//		  				{
//							yy_forecast[0][i] 	= (mHmiss*full_mBtTm_frcst')[0][i] + rann(1,1)*sqrt( mRmiss[0][0] );
//						}				
//
//		  }
//		}  // ffor (decl i=0; i<tstar; i++)
//
//
//		return {yy_nowcast, yy_forecast};
//}
///**********************************NOWCASTING ALL VARIABLES********************************************************/









main()
{
decl sdates= {
						"2000q2", "2000q3", "2000q4",	"2001q1", "2001q2", "2001q3", "2001q4",	"2002q1", "2002q2", "2002q3", "2002q4",	"2003q1", "2003q2", "2003q3", "2003q4",	"2004q1", "2004q2", "2004q3", "2004q4",	
						"2005q1", "2005q2", "2005q3", "2005q4",	"2006q1", "2006q2", "2006q3", "2006q4",	"2007q1", "2007q2", "2007q3", "2007q4",	"2008q1", "2008q2", "2008q3", "2008q4",	"2009q1", "2009q2", "2009q3", "2009q4",	"2010q1", "2010q2", "2010q3", "2010q4",	
						"2011q1", "2011q2", "2011q3", "2011q4",	"2012q1", "2012q2", "2012q3", "2012q4",	"2013q1", "2013q2", "2013q3", "2013q4",	"2014q1", "2014q2", "2014q3", "2014q4",	"2015q1", "2015q2", "2015q3", "2015q4",	"2016q1", "2016q2", "2016q3", "2016q4", 
						"2017q1", "2017q2", "2017q3", "2017q4",	"2018q1", "2018q2", "2018q3", "2018q4",	"2019q1", "2019q2", "2019q3", "2019q4",	"2020q1", "2020q2", "2020q3", "2020q4",	"2021q1", "2021q2", "2021q3", "2021q4", "2022q1", "2022q2", "2022q3", "2022q4",
						"2023q1", "2023q2", "2023q3", "2023q4", "2024q1", "2024q2", "2024q3", "2024q4"};

//sdates = sdates[120:];


/*data_name      0          1    2     3        4     5      6        7            8         9          10    	 11
           = {"rGDPnew", "IP","PMI","ElekUr","RT","THC_C","EMPNA","KapasiteKO",   "XQ",      "MQ",    "XQVal","MQVal",
	     	 12        13	    14	       15	        16	   17	   18      	19	      20	                21      	   	  22   23	  24		  25		  26
		"rbist100","rforexr","bistvol","pri-earning","conf","int1m","treauc","cds","termspread_1y_1m","spread_tr3m_libor3m","msci_em","XR","credit","credit_bus","credit_other",
	    	 27		28	    29	  30	  31	32		33	   34		35		36		37		38		39		40		 41		  42	   43	  44	   45	  46	
			"RT1", "RT2", "RT3", "RT4", "RT5", "RT6", "RT7", "RT8"  , "THC1", "THC2", "THC3", "THC4", "Myat", "Mara", "Mimal", "Econf", "Sconf", "Rconf", "PV3", "ENP3",
	         47		    48		 49	      50
			"Ipman", "Ipint", "Ipdur", "Ipndur"};  */


data_name  //  0          1       2     3        4     5      6        7            8         9          10    	 11
           = {"rGDPnew", "IP","PMI","ElekUr","RT","THC_C","EMPNA","KapasiteKO",   "XQ",      "MQ",    "XQVal","MQVal",
	  //	 12        13	    14	       15	        16	   17	   18      	19	      20	                21      	   	  22   23	  24		  25		  26
		"rbist100","rforexr","bistvol","pri-earning","Rconf","int1m","treauc","cds","termspread_1y_1m","spread_tr3m_libor3m","msci_em","XR","credit","credit_bus","credit_other",
	  //	 27		28	    29	 	 30      31		  32	   33	   34	    35		  36	 
			"RT4", "RT6", "RT8"  , "THC2", "THC4", "MQyat", "MQara", "Econf", "Ipint", "Ipdur"};

selection_ = <0, 1, 2, 3, 4, 5, 6, 7, 8,9      ,12, 13, 16, 24, 26,      27, 28, 29, 30, 31, 32, 33, 34, 35, 36>;  	 // with X M indexes with XR
// selection_ = <0, 1, 2, 4, 5, 6, 7, 8,9      ,12, 13, 16, 24, 26,      27, 28, 29, 30, 31, 32, 33, 34, 35, 36>;  	 // with X M indexes with XR
//selection_ = <0, 1, 2, 3, 4, 5, 6, 7, 8,9      ,12, 13, 16, 24, 26>;  	 // with X M indexes with XR       




////               0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27   
data_freq      = {"Q","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M","M"    ,"M","M","M","M","M","M","M","M" ,"M","M","M","M","M","M","M","M","M","M","M","M" ,"M","M","M","M"   ,"M","M","M","M"};

////	           0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27  
data_typeI     = {"F","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S","S"    ,"S","S","S","S","S","S","S","S" ,"S","S","S","S","S","S","S","S","S","S","S","S" ,"S","S","S","S"   ,"S","S","S","S"};

////	           0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27   
data_typeII    = {"H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H","H"    ,"H","H","H","H","H","H","H","H" ,"H","H","H","H","H","H","H","H","H","H","H","H" ,"H","H","H","H"    ,"H","H","H","H"};															  

data_typeIII   = {"0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0","0"    ,"0","0","0","0","0","0","0","0" ,"0","0","0","0","0","0","0","0","0","0","0","0" ,"0","0","0","0"    ,"0","0","0","0"};															  

////	          0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27  
//data_trans  = {"G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G","G"};

////	          0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27  
data_trans    = {"D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D","D"     ,"D","D","D","D","D","D","D","D"  ,"D","D","D","D","D","D","D","D","D","D","D","D"  ,"D","D","D","D"   ,"D","D","D","D"};



	  //	  0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15  16  17  18  19  20  21  22  23  24  25  26  27  
data_Qahead= <0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0          ,  0,  0,  0,  0,  0,  0,  0,  0  ,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0  ,  0,  0,  0,  0   ,  0,  0,  0,  0>;

		 


/*************************************************				
1 Real Gross Domestic Product              				quarterly 
2 Industrial Production Index              				monthly 
3 Purchasing Manager Index, Manufacturing  				monthly 
4 Real Disposable Personal Income         				monthly 
5 Unemployment Rate                        				monthly 
6 Employment, Non-farm Payrolls            				monthly 
7 Personal Consumption Expenditure         				monthly 
8 Housing Starts                             			monthly 
9 New Residential Sales                      			monthly 
10 Manufacturers’ New Orders, Durable Goods  			monthly 
11 Producer Price Index, Finished Goods      			monthly
12 Consumer Price Index, All Urban Consumers 			monthly 
13 Imports 												monthly 
14 Exports 												monthly 
15 Philadelphia Fed Survey, General Business Conditions monthly 
16 Retail and Food Services Sales 						monthly 
17 Conference Board Consumer Confidence 				monthly
**************************************************/

						
decl Datapath = "data/DataSet_1024.xlsx";

decl data = new Database();
	 data.Load(Datapath);

	 
decl dSTARTYEAR  = 2000;
decl dFINALYEAR  = 2024;
decl dSTARTMONTH =    1;
decl dFINALMONTH =   10;
frcst 		 	 =	 15;
hrzn 			 = frcst/3;

decl Month="M"+sprint(dFINALMONTH);
decl  Year="Y"+sprint(dFINALYEAR);
 

/***************General setup**************************/
save        	= 0;
printorder  	= 1;
printorder2 	= 0;
printorder_mh 	= 0;
draworder		= 1;
SV_fac			= 1;      	//stochastic volatility	on factor
SV_gdp			= 1;      	//stochastic volatility	on gdp measurement equation
SV_m			= 0;		//stochastic volatility	on monthly measurement equation
nonNan			= 0;
StDev_in_Standardization = 0;
doft_f = 15;
/***************General setup **************************/
std_rt = 1;



decl ModelNo = "TR_GDP_";

//selection_ = selection_~ selection_V; 									  
//decl numb  = columns(selection_V);

data.Select(0,      data_name   [selection_]);   
vfreqY_           = data_freq   [selection_];
vTypeIY_          = data_typeI  [selection_];
vTypeIIY_         = data_typeII [selection_];
vTypeIIIY_        = data_typeIII[selection_];	





Start_t0 = 0;
data.SetSelSample(dSTARTYEAR, dSTARTMONTH, dFINALYEAR, dFINALMONTH);
freq  		 = 12;
decl mFullData   = (data.GetGroup(0)[][]);	     	 // println(mFullData[25:30][]);

decl Mean_Data = mFullData[][                         : columns(mFullData)-1]; //println(Mean_Data[25:30][]);	// exclude the survey vols		  

mMVAL 		 = 999999999;

decl time0=timer();
decl time1;
decl time01,time02;


/**********SETUP MCMC SAMPLER *******************************/
//decl predsample = 509;		 	 //	509	  			 98 & 607 // 1977 M1 -> 2019 M6	  total 510
//decl predsample = 533;		 	    //	509	  			 98 & 607 // 1977 M1 -> 2019 M6	  total 510
decl predsample = 0;		 	    //	509	  			 98 & 607 // 1977 M1 -> 2019 M6	  total 510
decl dTFullsample = sizer(Mean_Data);		   //println(dTFullsample);
decl Startt       = dTFullsample-predsample;
decl dEvalT       = sizec(Mean_Data')-Startt+1;
				
decl BURNIN = 1000;                    	//NUMBER OF DRAWS TO LEAVE OUT
decl NDRAW  = 2000;                   	//NUMBER OF DRAWS
decl THIN   = 1;                    	//EVERY L-TH VALUE IS USED
decl MCMC   = BURNIN + NDRAW;         	//TOTAL NUMBER OF DRAWS



tres    	= 10^(-10);   
facnu		=  1;    // # of factors
lagof	 	=  1;	 // # of lags of factors
nolfq     	=  0;	 // # of lags of quarterly flow factors recuired in state vector
nolsq     	=  0;	 // # of lags of quarterly stock factors recuired in state vector
nolfm 		=  0;	 // # of lags of monthly factors recuired in state vector

if( nolfm < lagof-1 )
	{	nolfm = max(lagof-1,nolfm);   }

 //        flow q + q lag	        							   + monthly and   monthly lags
dimf = (2*facnu)  + (2*facnu)*nolfq + (1*facnu)  + (1*facnu)*nolsq + facnu + facnu*nolfm;		//println(" dimf ",dimf );		  

StateSel    = zeros(1,facnu);
for(decl i=0; i<facnu; i++)	 {	StateSel[i] = 2*facnu+(2*facnu)*nolfq + 1*facnu+(1*facnu)*nolsq + i;   }

/****************************************** PRIOR DISTRIBUTIONS ******************************************/
/*Butun coef ler icin standard normal, varyanslar icin noninformative */
decl phivar_		= unit( (facnu^2)*lagof )*10^(-1);
decl phihat_		= 0.5*ones((facnu^2)*lagof,1);             //Autoregressive coefficients of the coincident factors
			   	
decl vparhat_ 		= zeros(facnu,1);					 // For factor loadings standard normal
decl mparvar_ 		= unit(facnu)*10^(1);

decl Sigma2y_dof_   = facnu + 1;
decl Sigma2y_Scale_	= 10^(-6);

decl Sigma2B_dof_   = 0;
decl Sigma2B_Scale_ = 0;

dof_er    			= 0;
scale_er  			= 0;
/****************************************** PRIOR DISTRIBUTIONS ******************************************/




decl excelfile_nowcast		= .NaN*zeros( 1000, sizec(Mean_Data')-Startt+1 + 1);					//println(  " sizec(Mean_Data')-Startt+1 ",sizec(Mean_Data')-Startt+1);
decl excelfile_nowcast_ns	= .NaN*zeros( 1000, sizec(Mean_Data')-Startt+1 + 1);

decl excelfile_nowcast_fill		= .NaN*zeros((sizec(Mean_Data')-Startt+1  ), 2);			//println(  " sizec(Mean_Data')-Startt+1 ",sizec(Mean_Data')-Startt+1);

decl exf_now_ns_fill = new array [hrzn];
decl LLIKE_PR_MM 	 = new array [hrzn];
decl LLIKE_PRDENS_MM = new array [hrzn];
decl I_MM			 = new array [hrzn];
decl inf_pr_MM 		 = new array [hrzn];

for(decl i = 0; i<hrzn; i++)
{
//	 LLIKE_PR_MM	[i]	= .NaN*zeros( dEvalT, NDRAW);
//	 LLIKE_PRDENS_MM[i]	= .NaN*zeros( dEvalT, NDRAW);
	 LLIKE_PR_MM	[i]	= .NaN*zeros( 1,      NDRAW);
	 LLIKE_PRDENS_MM[i]	= .NaN*zeros( 1,      NDRAW);
	 I_MM			[i]	= .NaN*zeros( dEvalT, NDRAW);
	 inf_pr_MM		[i]	= .NaN*zeros( dEvalT, NDRAW);
	 exf_now_ns_fill[i]	= .NaN*zeros( dEvalT, 1);			//println(  " sizec(Mean_Data')-Startt+1 ",sizec(Mean_Data')-Startt+1);
}

decl mdensh0 			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mdensh1 			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mdensh2 			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mdensh3 			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mdensh4 			=  .NaN*zeros( dEvalT, NDRAW/THIN);

decl mPLh0   			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mPLh1  	 		=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mPLh2   			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mPLh3   			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl mPLh4   			=  .NaN*zeros( dEvalT, NDRAW/THIN);

decl varr_MM   			=  .NaN*zeros( dEvalT, NDRAW/THIN);
decl LLIKE_ML  			=  .NaN*zeros( dEvalT, 1);		
decl LLIKE_ML1 			=  .NaN*zeros( dEvalT, 1);	
decl LLIKE_ML2 			=  .NaN*zeros( dEvalT, 1);	
decl LLIKE_ML3 			=  .NaN*zeros( dEvalT, 1);	

/* ? */
decl PHI_ALL  			= .NaN*zeros( dEvalT, 1);
decl LAMBDAQ_ALL  		= .NaN*zeros( dEvalT, 1);
decl PHI_ALL_SIM  		= .NaN*zeros( dEvalT, NDRAW/THIN);
decl LAMBDAQ_ALL_SIM  	= .NaN*zeros( dEvalT, NDRAW/THIN);
/* ? */

decl k;	decl Endt = dTFullsample;
/****************Setup of the recursion ***************************/
decl y_gdp_comp, y_gdp_spf_comp;
decl densh0, densh1, densh2, densh3, densh4;

/*KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK*/
/*KKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKKK*/
decl kk;  decl kkend =  Endt-Startt;	           // //println(" kkend ",kkend);

	for(kk = 0; kk < kkend+1 ; kk++)  
	{
			decl k = kk+Startt;
			println("-------------------------------------Observation = ", k-1 ,"------------------");
	
			MHphi_acc	= 0;
			//println(      Mean_Data[:k-1][]        );
	
			decl indexx = zeros(1,sizec(Mean_Data));
			for(decl j = 0; j<sizec(Mean_Data); j++)  // Select those variables with more than 12 observations
				{
					decl index_y = vecindex( (Mean_Data[:k-1][j]) .!= mMVAL);
					indexx[j] = rows(index_y) .> 12;	 //println( " index_y ", index_y);
				}	 //println(" indexx ",  indexx);

			decl inde = vecindex(indexx .==1);   //println(" inde ",  inde);
			decl mSelData  = Mean_Data[][inde];	 //println(mSelData);

			selection = selection_[inde];	   
 			vfreqY    = vfreqY_    [inde];
 			vTypeIY   = vTypeIY_   [inde];
 			vTypeIIY  = vTypeIIY_  [inde];
 			vTypeIIIY = vTypeIIIY_ [inde];

			nov   	  = sizec(mSelData);
			n_qf 	  = 0;
			n_qfs1	  = 0;
			n_m		  = 0;

			for (decl i = 0; i<nov; i++)
			{
				if 		( (vfreqY[i] == "Q") && (vTypeIY[i] == "F") )
					{ 	n_qf = n_qf+1;
							 if( (vTypeIIY[i] == "S") && (vTypeIIIY[i] == "1") )
								 {n_qfs1 = n_qfs1+1;}
					}
				else if ( vfreqY[i] == "M"                          )
					{ n_m = n_m + 1; }
			}

			n_qfs = n_qfs1;
			n_qfh = n_qf - n_qfs; 
			n_q   = n_qf+n_qs;
			
			no_vec = zeros(1, 4);
			no_vec[1] = n_qf;
			no_vec[2] = n_qs;
			no_vec[3] = n_m;	 //println("n_m",n_m);
  
			//number_fb = sumr(no_vec[1:] .!= 0);   //number of factor block
			number_fb = 3;                        //n_qf, n_qs, n_mf, n_ms, n_wf, n_ws, n_d;
			
			//println(" n_qfh ", n_qfh, " n_qfs1 ", n_qfs1 , " n_qfh + n_qfs1 ", (n_qfh + n_qfs1)  );
			//println(" n_qfs ", n_qfs," n_qs ", n_qs , " n_qf ",n_qf, " n_m ", n_m, " n_qfs1 ", n_qfs1);

		    //VOL_Data  =	vol_Data__[:k-1][];
			decl mSelDatat = mSelData[:k-1][];	  //println(mSelDatat);
                  dSampleT = sizer(mSelDatat);


			/********************************************************************************************* SETUP MCMC SAMPLER *********************************************************************************************/
			if(kk == kkend)		  // We take the last available rgdp up to today to compare nowcasts
				{
					y_gdp_comp = mSelDatat[][0];

					if(n_qfs>0)
					{	 y_gdp_spf_comp = mSelDatat[][1];   }
				}
			/********************************************************************************************* SETUP MCMC SAMPLER *********************************************************************************************/
			

		   /********************************************************* MIMIC REAL TIME - ESTIMATION 29.DAY OF THE MONTH ********************************************************************/
			for(decl i=0; i<nov; i++)
		   {
//				if(     (data_name[selection[i]] == "rGDPnew" ) || (data_name[selection[i]] == "rFCnew")        )
//				 {	 mSelDatat[dSampleT-3:dSampleT-1] [i] = mMVAL;}
//			
//				else if( (data_name[selection[i]] == "IP") || (data_name[selection[i]] == "MQ")|| (data_name[selection[i]] == "XQ")|| (data_name[selection[i]] == "RT")|| (data_name[selection[i]] == "pri-earning")  )
//				{   mSelDatat[dSampleT-1:dSampleT-1] [i] = mMVAL;   }
//				else if( (data_name[selection[i]] == "EMPNA")   )
//				{   mSelDatat[dSampleT-2:dSampleT-1] [i] = mMVAL;   }
			//	else if( (data_name[selection[i]] == "termspread_1y_1m") || (data_name[selection[i]] == "spread_tr3m_libor3m")|| (data_name[selection[i]] == "msci_em")
			//	|| (data_name[selection[i]] == "stock-em-tr")|| (data_name[selection[i]] == "bond-em-tr")|| (data_name[selection[i]] == "conf")  )
			//	{   yy1[T-1:T-1] [i] = mMVAL;   }
		   } // for
	/********************************************************* MIMIC REAL TIME - ESTIMATION 29.DAY OF THE MONTH ********************************************************************/

			/***********************************************************************************************/
			/***********************RGDP********************************************************************/	
			selection_pr		= <0, 1>;

			decl data_pr = new Database();		   
	        data_pr.Load(Datapath);

//			decl data_name_pr   = {"_1","_2"};
			decl data_name_pr   = {"rGDPnew","IP"};
			//decl dFINALYEAR_pr  =  2019;
			//decl dFINALMONTH_pr =    12;

			decl dFINALYEAR_pr  = dFINALYEAR  + idiv(dFINALMONTH + (frcst-3), 13);
			decl dFINALMONTH_pr = (imod(dFINALMONTH + (frcst-3), 13) ) + idiv(dFINALMONTH + (frcst-3), 13);
			//println(" dFINALYEAR  "		, dFINALYEAR);	  		//println(" dFINALMONTH "		, dFINALMONTH);
			//println(" dFINALYEAR_pr  "	, dFINALYEAR_pr);  		//println(" dFINALMONTH_pr "	, dFINALMONTH_pr);			

			data_pr.Select(0,     data_name_pr[selection_pr]);  
			data_pr.SetSelSample(dSTARTYEAR, dSTARTMONTH, dFINALYEAR_pr, dFINALMONTH_pr);
//			yy_0   = data_pr.GetGroup(0)[][];	   
								   
			yy_gdp		 	 	= data_pr.GetGroup(0)[][0];
			yy_gdp_stndrdzd 	= data_pr.GetGroup(0)[][0];

			decl index       	= vecindex(mSelDatat[][0] .!= mMVAL);
			decl now_index		= zeros(hrzn,1);
			for(decl k = 0; k<hrzn; k++)
				{
					now_index[k]  	= index[rows(index)-1] + 3*(k+1); // - 1;
				} // 	 println( " index ",index," now_index ",now_index);
			decl index_pr 	 	= index|now_index;
		
			decl tmp 	     	= (yy_gdp|zeros(30,1))[index_pr];
			decl Ttmp        	= sizer(tmp);			   	
			decl ltrend      	= range(1, Ttmp, 1)';  decl qtrend = sqr(ltrend); 
			decl tmpx        	= ones(Ttmp,1);//~ltrend~qtrend;
			decl beta        	= invertsym(tmpx'tmpx)*tmpx'*tmp;	        	  

			/***********************************************************************************************/
			decl tmp2 	     	= yy_gdp[index];	  								
			decl Ttmp2        	= sizer(tmp2);			   	
			decl ltrend2      	= range(1, Ttmp2, 1)';  decl qtrend2 = sqr(ltrend2); 
			decl tmpx2        	= ones(Ttmp2,1);//~ltrend~qtrend;
			decl beta2        	= invertsym(tmpx2'tmpx2)*tmpx2'*tmp2;	        	  
				 tmp2         	= tmp2 - tmpx2*beta2;
			decl std_gdp2     	= moments(tmp2)[2];
			 	 tmp2           = tmp2./std_gdp2;
			decl yy_gdp_st2   	= mMVAL*ones(rows(yy_gdp), 1);
			yy_gdp_st2[index]   = tmp2;
			/***********************************************************************************************/

			yy_gdp       	 	= mMVAL*ones(rows(yy_gdp)+30, 1);		        
			yy_gdp[index_pr] 	= tmp;
		    tmp             	= tmp - tmpx*beta;	
			decl mean_gdp   	= beta;
			decl std_gdp     	= moments(tmp)[2];
//			decl gdp_mean_pr    = mean_gdp;
//			decl gdp_std_pr     = std_gdp;

			if(StDev_in_Standardization == 0) {	 tmp = tmp;	         }
			else			                  {	 tmp = tmp./std_gdp; }

			yy_gdp_stndrdzd   		  = mMVAL*ones(rows(yy_gdp), 1);
			yy_gdp_stndrdzd[index_pr] = tmp;
//			println( yy_gdp_stndrdzd ~ yy_gdp ~ mSelDatat[][0]);
			/***********************RGDP********************************************************************/
			/***********************************************************************************************/
			
			decl out     = TRANSFORM_DATA(mSelDatat, nov, data_name, selection, freq);				// Transforming data into linearly detrended standardized data
		    yy      = out[0]';		 	        								    // Start_t0 from 2001:09  if decl dSTARTYEAR  = 2001   &    decl dSTARTMONTH = 8	 
		 	slope_l = out[1]';
		    std_l   = out[2]';
		    meany_l = out[3]';
		    indy_l  = out[4]';
	   decl yy1_gro = out[5] ;

			mY_mean   = meany_l;
			mY_stddev = std_l;


													   
            /***************************************************INITIAL VALUES FOR THE GIBBS SAMPLER (for kk=0) **************************************************/
			omt_gdp   =  rangamma(dSampleT+frcst, 1, (doft_f + 1)/2, (  doft_f + 1 )/2 );
			omt	      =  rangamma(dSampleT+frcst, 1, (doft_f + 1)/2, (  doft_f + 1 )/2 );
			
			vVarym      		= 0.1 *ones(nov, 1);
			mlambdam_qf    		= 0.1 *ones(n_qf, 1*facnu) ~ zeros(n_qf, 1*facnu);
			mlambdam_qs    		= 0.5 *ones(n_qs, 1*facnu) ~ zeros(n_qs, 1*facnu);	
			mlambdam_m    		= 0.25*ones(n_m , 1*facnu);
			decl mlambdam 		= 0.25*ones(nov,  1*facnu);
			vlambdam_rgdp		= 0.1 *ones(1,  1*facnu);
			
			/********************************************************************************************************************************initial values************************************************************************************************************************************/
			if ((kk>0)&&(facnu<2))
			{
				for(decl i=0; i<nov; i++)
				{
					if(i==0)
					{
			//			println( 	  " n_m ",n_m, " n_q ", n_q, " nov ",nov );
						mlambdam_qf    		= 0.1*ones(n_qf, 1*facnu) ~ zeros(n_qf, 1*facnu);
						decl index       	= vecindex(yy'[][0] .!= mMVAL);
						decl tmp_y 	     	= yy'  [index[:rows(index)-3]][i];	                                //println(index[:rows(index)-3]);								
						decl tmp_x 	     	= mBtTm[index[:rows(index)-3]][facnu*(1-1):facnu*1-1];	  								
						decl m1,v1;
						olsc(tmp_y, tmp_x, &m1, &v1);
			//			mlambdam_qf	[][0] = m1.*ones(n_qf, 1*facnu) ;
						mlambdam_qf	[0][0] = m1;
						decl res1 = tmp_y-m1*tmp_x;
			//			vVarym		[0:n_q-1] = res1'res1/rows(tmp_y).*ones(n_qf, 1*facnu) ;
						vVarym		[0] = res1'res1/rows(tmp_y);
						vlambdam_rgdp =	mlambdam_qf	[0][0];
					}
			//		if(i==0){ decl kl;}
					else if(i>n_q-1)
					{
						decl index       	= vecindex(yy'[][i] .!= mMVAL);
						decl tmp_y 	     	= yy'[index[:rows(index)-5]][i];	  								
						decl tmp_x 	     	= mBtTm[index[:rows(index)-5]][facnu*(3-1):facnu*3-1];	  								
						decl m1,v1;
						olsc(tmp_y, tmp_x, &m1, &v1);
						mlambdam_m	[i-n_q] = m1 ;
						decl res1 = tmp_y-m1*tmp_x;
						vVarym		[i]	  = res1'res1/rows(tmp_y) ;
					}
				}
			}
			/*********************************************************************************************************************************************************************************/

			decl var_factor_t 	= 0.1*ones((dSampleT + frcst),1)**unit(facnu);
			decl omt_f          =	  ones((dSampleT + frcst),1)**unit(facnu);
			decl var_gdp_t 		= 0.1*ones(dSampleT + frcst,1);	
			var_m_t 			= 0.1*ones(dSampleT + frcst,n_m);	
			res_gdp 			= 0.1*ones(dSampleT + frcst,1);	
			ht_gdp 				= 0.1*ones(dSampleT + frcst,1);
			ht_gdpT 			= 0.1*ones(frcst,1);
			var_gdp				= 0.1*ones(1,1);
			//var_factor_t 			= 0.1*unit(facnu);
			vVarym      		= 0.1*ones(nov, 1);
			mPhim       		= 0.9*ones(facnu, facnu*lagof);
			//mPhim = vecr(mPhim);
			mVarStm     		= unit(facnu);   
			decl vBtT0m 		= zeros(dimf, 1);
			decl PtT0m  		= 0;
			decl result1, result2, result5, result6, result7, result20 ;							   
            /***************************************************INITIAL VALUES FOR THE GIBBS SAMPLER (for kk=0) **************************************************/
			
			XtT0SV_f	= 0.1;  
			PtT0SV_f	= 0.1;  
			dSigSV_f 	= 0.1;  
			dPhiSV_f 	= 1; 
			dMuSV_f 	= 0;    
			
			XtT0SV	= 0.1;
			PtT0SV	= 0.1;
			dSigSV 	= 0.1;
			dPhiSV 	= 1;
			dMuSV 	= 0;
			
			XtT0SV_m	= 0.1;  
			PtT0SV_m	= 0.1;  
			dSigSV_m 	= 0.1;  
			dPhiSV_m	= 1; 
			dMuSV_m 	= 0;
			
//			vSigmay_vl 	 = 0.1*ones(numb,1); 	 //println(" vSigmay_vl ",vSigmay_vl);
//			vSigmay_vl_f = 0.1*ones(numb,1); 	 //println(" vSigmay_vl ",vSigmay_vl);
//			vSigmay_vl_m = 0.1*ones(numb,1); 	 //println(" vSigmay_vl ",vSigmay_vl);
			mmnt	   = 1;
			/********************************************************************************************************************************initial values************************************************************************************************************************************/



			
			/***************************************************STORAGE SPACES  ***************************************************/
			decl BtTMM   	= new array[number_fb*facnu];
				for(decl i=0;i<number_fb*facnu;i++)
				{
					BtTMM[i]    = zeros(dSampleT    		  ,NDRAW/THIN);
				}
			
			
			decl FORECAST_ORG   = new array[nov];
			
				for(decl j  	= 0; j<nov; j++)
				{
					FORECAST_ORG[j] = zeros(dSampleT     			   ,NDRAW/THIN);
				}
			
			
			decl FORECAST_ORG_frcst   = new array[nov];
			
				for(decl j  	= 0; j<nov; j++)
				{
					FORECAST_ORG_frcst[j] = zeros(dSampleT+frcst    			   ,NDRAW/THIN);
				}
				
			decl PHIMM    			= zeros(lagof*facnu^2 	 ,NDRAW/THIN);
			decl LAMBDAQMM    		= zeros(	  1 		 ,NDRAW/THIN);
			decl SIG2_FACVOL  		= zeros(	  1		 	 ,NDRAW/THIN);
			decl VAR_GDP_T_MM  		= zeros(dSampleT+frcst 	 ,NDRAW/THIN);
			decl VAR_FACTOR_T_MM  	= zeros(dSampleT+frcst 	 ,NDRAW/THIN);
			decl RES_GDP_MM  		= zeros(dSampleT+frcst 	 ,NDRAW/THIN);
			decl ht_GDP_MM  		= zeros( dSampleT+frcst  ,NDRAW/THIN);
			decl ht_GDPT_MM  		= zeros(	  frcst 	 ,NDRAW/THIN);
			decl var_gdp_MM  		= zeros(	  1 	     ,NDRAW/THIN);
			decl inf_MM  			= zeros(dSampleT+frcst 	 ,NDRAW/THIN);
			decl   R_MM  			= zeros(dSampleT+frcst 	 ,NDRAW/THIN);
			decl SIG2YMM  			= zeros(nov   			 ,NDRAW/THIN);
			decl SIG2_GDPVOL  		= zeros(1   			 ,NDRAW/THIN);
			decl LAMBDAFMM  		= zeros((nov-n_qfs)*facnu,NDRAW/THIN);
			decl LAMBDAFMMst		= zeros((nov-n_qfs)*facnu,NDRAW/THIN);
			decl LLIKEMM  			= zeros(1                ,NDRAW/THIN);
			decl LLIKE_RGDP_MM 		= zeros(1                ,NDRAW/THIN);
			decl noclMM     		= zeros(1                ,NDRAW/THIN);
            /***************************************************STORAGE SPACES  ***************************************************/

			/**********************************filled******************************************************************************************************/
			decl cumul = (cumulate(no_vec'))';				////println(cumul," cumul ",cumul[number_fb-1]);
			
				aIndex = new array[number_fb];
			
				for (decl i=0; i<number_fb; i++)
				{
			//		aIndex[i]  = vecindex(yy[cumul[i]][] .!= mMVAL);				
					aIndex[0]  = vecindex(yy[cumul[0]][] .!= mMVAL);				
					aIndex[1]  = vecindex(yy[cumul[0]][] .!= mMVAL);				
					aIndex[2]  = vecindex(yy[nov-1][] 	 .!= mMVAL);				
				}
			/**********************************filled******************************************************************************************************/

			time01=timer();	
  			/********************************************************************************************** Start MCMC Sampling ******************************************************************************************************/
			for (decl i=0; i<MCMC; i++ )
				{
									decl Tt = sizec(yy);
									decl yy_star;
									yy_star = yy;	
								
								// end of the month
								
									decl out     = SAMPLE_BtT(vBtT0m, PtT0m, yy_star, frcst, now_index, var_gdp_t, var_factor_t, omt_f, mlambdam);
									mBtTm        = out[0];	                        //println( "mBtTm ", mBtTm[sizer(mBtTm)-6:][]);
									decl full_mBtTm	      = out[1];	  	            //mBtTm =  standardize(mBtTm);     //println(mBtTm);	  	//	mBtTm[][0] = standardize(mBtTm[][0]);
									decl l_like  		  = out[2];					if(printorder==1) {		println("log likelihood ",	 		l_like)		 ;}
									decl l_like_rgdp  	  = out[9];  			 	if(printorder==1) {		println("log likelihood rgdp ", 	l_like_rgdp) ;}	    
									decl l_like_ip  	  = out[10];  			 	//if(printorder==1) {		println("log likelihood ip ", 		l_like_ip);	 	println("log likelihood sum ", l_like_ip + l_like_rgdp);}   
								
									decl l_like_pr  	  = out[11];  		        //println( l_like_pr);	   
									decl y1t_sim  		  = out[12];  			 	if(printorder==1) {		println("%r", {"rGDP_q0","rGDP_q1","rGDP_q2","rGDP_q3","rGDP_q4"}, y1t_sim); 			 }	  	 	 	 
																					  //println("%r", {"rGDP_q0","rGDP_q1","rGDP_q2","rGDP_q3","rGDP_q4"}, y1t_sim); 
									inf_				  = out[13];
									R_					  = out[14];
									inf_pr				  = out[15];
									decl I_sim			  = out[16];
									decl var_sim		  = out[17];
									
									decl mBtt    		  = out[5];
									decl mKtt    		  = out[6];
								
									decl mBtTm_frcst 	  = out[7];			     			//println( " mBtTm_frcst[][] ", mBtTm_frcst);
									decl full_mBtTm_frcst = out[8];			     			//println( " mBtTm_frcst[][] ", mBtTm_frcst);
								//	decl frcst_fact_qf = mBtTm_frcst[][			:facnu-1];
								//	decl frcst_fact_m  = mBtTm_frcst[][facnu	: 		];
								
									if(n_qfs==0)
										{
											mPhim 		= SAMPLE_PHII(phihat_, phivar_, vBtT0m, var_factor_t, omt_f)[0];
										}
									else{
											decl out_phi = SAMPLE_PHI_MH(phihat_, phivar_, vBtT0m, mPhim, yy_star, MHphi_acc, var_gdp_t, var_factor_t, omt_f, mlambdam);
											mPhim  		 = out_phi[0];
											MHphi_acc    = out_phi[1]; 
										}
//									mPhim = 0;	
										
										decl outf       = SAMPLE_FAC_VAR(dof_er, scale_er, frcst, mBtTm_frcst, var_factor_t);
										var_factor_t 	= outf[0];		        //println("var_factor_t : " , var_factor_t);
										omt_f			= outf[1];				//println((omt_f[sizer(omt_f)-20:][]));
									//	var_factor_t 	= 1*unit(facnu);
									
										if (printorder == 1){	println("vPhi : ", "%13.6f" , mPhim);   }
									//	if (printorder == 1)	{	println("var_factor_t : ", "%13.6f" , var_factor_t);   }


										/************************ Sample Factor Loadings and Variances of Monthly Variables, Indicator is set to 3 ***************************/
										result20     	= SAMPLE_LAMBDA_VOL_NoSurvey(vparhat_, mparvar_, Sigma2y_dof_, Sigma2y_Scale_, yy_star, mBtTm, 3, var_gdp_t, index_pr);
										mlambdam_m  	= result20[0];		   //println("here 1 ", mlambdam_m);
										vVarym_m    	= result20[1];
										mlambdam_m_st 	= result20[2];	  							
										/************************ Sample Factor Loadings and Variances of Monthly Variables, Indicator is set to 3 ***************************/


										/************************ If no survey info is used, Sample Factor Loadings and Variances of GDP, Indicator is set to 1 ***************************/
										if(n_qfs==0)
											{
												result1     	= SAMPLE_LAMBDA_VOL_NoSurvey(vparhat_, mparvar_, Sigma2y_dof_, Sigma2y_Scale_, yy_star, mBtTm, 1, var_gdp_t, index_pr);					 
												vlambdam_rgdp   = result1[0];
												mlambdam_qf 	= vlambdam_rgdp~zeros(no_vec[1],facnu);  //println(" here 2 ",vlambdam_rgdp);
												vVarym_qf   	= result1[1];
												res_gdp         = result1[3];
												ht_gdp          = result1[4];
												ht_gdpT         = result1[5];
												var_gdp_t       = result1[6];
												
												mlambdam    = vlambdam_rgdp|mlambdam_m; 	 //println(" here 3 ", mlambdam);
												mlambdam_st = result1[2]|mlambdam_m_st; 
												vVarym 		= vVarym_qf | vVarym_m ;  	//println(  " vVarym_qf ", vVarym_qf);
											}
										/************************ If no survey info is used, Sample Factor Loadings and Variances of GDP, Indicator is set to 1 ***************************/	
		

											if (printorder == 1)
											{																														   
												print("%c", {"f1 Load st", "f1 Load", "\sigma^2_u"}, "%r",	data_name[selection_], "%10.2f", mlambdam_st~mlambdam);
												print("%c", {"\sigma^2_u"}, "%r",	data_name[selection_], "%10.2f", vVarym);			
											}
	
											decl result 	 	= NOWCAST(frcst, yy_star, full_mBtTm, full_mBtTm_frcst, now_index, var_gdp_t, mlambdam);
											yy_nowcast  		= result[0];   //	println(yy_nowcast');
											yy_forecast     	= result[1];


											if(i > BURNIN - 1 && fmod((i - BURNIN),THIN) == 0 )
												{
														if(printorder==1) {		println("i > log likelihood rgdp ", 	l_like_rgdp) ;}
				
														for(decl j=0; j<number_fb*facnu; j++)
															{
															(BtTMM[j])       [][(i - BURNIN)/THIN] = mBtTm[][j];
															}
				//										for(decl j = 0; j<nov-n_qfs; j++)
														for(decl j = 0; j<nov; j++)
															{
															(FORECAST_ORG[j])[][(i - BURNIN)/THIN] = (yy_nowcast')[][j];
															}
										
				//										for(decl j = 0; j<nov-n_qfs; j++)
														for(decl j = 0; j<nov; j++)
															{	
															(FORECAST_ORG_frcst[j])		[][(i - BURNIN)/THIN] = (yy_forecast')[][j];
															}

														PHIMM			[][(i - BURNIN)/THIN]    = vec(mPhim);
										                SIG2_FACVOL		[][(i - BURNIN)/THIN]    = dSigSV_f;														
														if(facnu == 1){ LAMBDAQMM[][(i - BURNIN)/THIN]    = mlambdam[0];}
														VAR_GDP_T_MM	[][(i - BURNIN)/THIN]    = var_gdp_t;
														VAR_FACTOR_T_MM	[][(i - BURNIN)/THIN]    = var_factor_t;
														RES_GDP_MM		[][(i - BURNIN)/THIN]    = res_gdp;
														ht_GDP_MM		[][(i - BURNIN)/THIN]    = ht_gdp;
														ht_GDPT_MM		[][(i - BURNIN)/THIN]    = ht_gdpT;
														var_gdp_MM		[][(i - BURNIN)/THIN]    = var_gdp;
													
														inf_MM			[][(i - BURNIN)/THIN]    = inf_;
														R_MM			[][(i - BURNIN)/THIN]    = R_;
													
														LLIKEMM   		[][(i - BURNIN)/THIN]  	 = l_like;
														LLIKE_RGDP_MM   []  [(i - BURNIN)/THIN]  = l_like_rgdp;
													
														SIG2YMM			[][(i - BURNIN)/THIN]    = vVarym;
														SIG2_GDPVOL		[][(i - BURNIN)/THIN]    = dSigSV;
														LAMBDAFMM 		[][(i - BURNIN)/THIN]  	 = vec(mlambdam);
														LAMBDAFMMst 	[][(i - BURNIN)/THIN]  	 = vec(mlambdam_st);
													
	
														for(decl l = 0; l<hrzn; l++)
															{
																(LLIKE_PR_MM   	 [l])[][(i - BURNIN)/THIN]  = l_like_pr[l];	 //	println( " LLIKE_PR_MM   	[kk][(i - BURNIN)/THIN] ",LLIKE_PR_MM   	[kk][(i - BURNIN)/THIN]);	
//															    (LLIKE_PR_MM   	 [l])[][(i - BURNIN)/THIN]  = exp(log_PL[l]);	 //	println( " LLIKE_PR_MM   	[kk][(i - BURNIN)/THIN] ",LLIKE_PR_MM   	[kk][(i - BURNIN)/THIN]);	
															//	(LLIKE_PRDENS_MM [l])[kk][(i - BURNIN)/THIN]  = y1t_sim  [l];	 
//																(LLIKE_PRDENS_MM [l])[][(i - BURNIN)/THIN]  = (yy_forecast')[now_index[l]-1][0];
																(LLIKE_PRDENS_MM [l])[][(i - BURNIN)/THIN]  = (yy_forecast')[now_index[l]][0];
																(I_MM 			 [l])[kk][(i - BURNIN)/THIN]  = I_sim  	 [l];
															}
																(varr_MM )			 [kk][(i - BURNIN)/THIN]  = var_sim;
														
														if(facnu == 1)
															{
																(PHI_ALL_SIM )	   [kk][(i - BURNIN)/THIN] = vec(mPhim);
																(LAMBDAQ_ALL_SIM ) [kk][(i - BURNIN)/THIN]  = mlambdam[0];
															}
														for(decl l = 0; l<hrzn; l++)
															{
																(inf_pr_MM   	 [l])[kk][(i - BURNIN)/THIN]  = inf_pr[l];
															}
														
													}	   //if(i > BURNIN - 1 && fmod((i - BURNIN),THIN) == 0 )
	

													if (fmod(i,100) == 0) {	println("-------------------------------------Round = ", i-BURNIN ,"------------------");	   }
				}	 // for (decl i=0; i<MCMC; i++ )

				println( " Predictive log likelihood: ",log( meanr(    (LLIKE_PR_MM[0])[][] )  )  );	
				//println(" meanr LLIKE_PR_MM [kk][] ",meanr(	 log(LLIKE_PR_MM[0]) [kk][]  )		 );			 							
							
				time1=timer();
							
				decl time2 = timer();
				//println("hesap kitap ve grafik suresi: ", time2-time1);
				println("MCMC sampling baslagicinden beri gecen toplam sure:  ", floor((time2-time0)/3600), " min ",
				(time2-time0)/60 - floor((time2-time0)/3600)*60, "sec");

				decl meanVARCOVQMM         = meanr(SIG2_FACVOL);
				decl meanPHIMM             = meanr(PHIMM);				//println(" meanPHIMM ", meanPHIMM);
				decl meanLAMBDAQMM         = meanr(LAMBDAQMM);			//println(" meanLAMBDAQMM ", meanLAMBDAQMM);
				decl meanVAR_GDP_T_MM      = meanr(VAR_GDP_T_MM);
				decl meanSTDEV_GDP_T_MM    = meanr(sqrt(VAR_GDP_T_MM));				
				decl meanVAR_FACTOR_T_MM   = meanr(VAR_FACTOR_T_MM);		//println(meanVAR_FACTOR_T_MM);
				decl meanSTDEV_FACTOR_T_MM = meanr(sqrt(VAR_FACTOR_T_MM));	
				decl meanRES_GDP_MM        = meanr(RES_GDP_MM);
				decl meanht_GDP_MM         = meanr(ht_GDP_MM);
				decl meanht_GDPT_MM        = meanr(ht_GDPT_MM);
				decl meanvar_gdp_MM        = meanr(var_gdp_MM);
				decl mean_inf_MM           = meanr(inf_MM);
				decl mean_R_MM    	       = meanr(R_MM);
				
				decl meanBtTMM   	= new array[number_fb*facnu];
				for(decl i=0; i<number_fb*facnu; i++)  	{	meanBtTMM[i]  = meanr(BtTMM[i]);   }

				decl meanFORECAST_ORG = new array[nov];
				for(decl j = 0; j<nov; j++)
					{	decl index       = vecindex(yy'[][j] .!= mMVAL);      //println(index);
				//		decl tmp1        = yy'[index][i];
						meanFORECAST_ORG[j]       =  ( meanr(FORECAST_ORG[j])  )[index];
					}			

				decl meanFORECAST_ORG_frcst = new array[nov];
					for(decl j = 0; j<nov; j++)
					{
						if(nonNan==1)
						{
							decl w_na_frcst = FORECAST_ORG_frcst[j];
							decl count = rows(w_na_frcst);
							decl final = zeros(count,1);
							decl row_n;
								for(decl n = 0; n<count; n++)
								{
						    		row_n      = w_na_frcst[n][];
									decl indx  = vecindex(row_n .!= .NaN);    
									final[n]   = meanr(row_n[indx]);
								}
							meanFORECAST_ORG_frcst[j]       =    ( final );
				  		}
						else
				  		{
							meanFORECAST_ORG_frcst[j]       =    ( meanr(FORECAST_ORG_frcst[j]) );
						}
					}

				decl noclmean    = meanr(noclMM);
				decl noclvar     = varr (noclMM);

				decl RMSE_ns = 0;
				decl RMSE_s  = 0;

/****************************************************************** IN-SAMPLE ANALYSIS *****************************************************************************************************************/
				for(decl i=0; i<nov; i++)
				{
					decl index       = vecindex(yy1_gro[][i] .!= mMVAL);      //println(index);
					decl tmp1        = yy1_gro[index][i];
					decl tmp2        = (meanFORECAST_ORG[i]  );   //meanFORECAST_ORG[j] = (  ( meanr(FORECAST_ORG[j])  )[index];
					
					if(StDev_in_Standardization == 0)  	{ tmp2= tmp2	  	      + mY_mean[i]; }
					else		                    	{ tmp2= tmp2*mY_stddev[i] + mY_mean[i]; }
		
		//			println(" i ", i, tmp2);
					tmp1 = tmp1[Start_t0:];
					tmp2 = tmp2[Start_t0:];
		
						if(i==0){
		//					decl index_spf       = vecindex(yy1_gro[][i+1] .!= mMVAL);      //println(index);
		//					decl tmp_spf         = yy1_gro[index_spf][i+1];
		//					println(tmp1~tmp_spf);
		//					RMSE_spf =sqrt(sumsqrc(tmp1-tmp_spf));
		//					println(" RMSE_spf ",RMSE_spf);
							RMSE_ns = sqrt(sumsqrc(tmp1-tmp2));
		//					println(" RMSE_ns ",RMSE_ns);
		//					println(" RMSE_ns last half : ", sqrt(sumsqrc(	(tmp1-tmp2)[idiv(rows(tmp1),2):]	)));
		//					println(" RMSE_s ",RMSE_s);
		//					println(" RMSE_s last half : ", sqrt(sumsqrc(	(tmp1-tmp3)[idiv(rows(tmp1),2):]	)));
								}
		//			println(tmp2);			
					if(draworder ==1){	  DrawTMatrix(i, tmp1'|tmp2'    ,  {i} ,						 dSTARTYEAR, dSTARTMONTH + Start_t0, 12   , 0,2);			}                      
				}
				   ShowDrawWindow();
/****************************************************************** IN-SAMPLE ANALYSIS *****************************************************************************************************************/

/****************************************************************** OUT-OF-SAMPLE ANALYSIS *************************************************************************************************************/
				for(decl i=0; i<nov; i++)
				{
					decl index       = vecindex(yy1_gro[][i] .!= mMVAL);      //println(index);	  				
					decl tmp1        = yy1_gro[index][i];					  //tmp1= standardize(tmp1);
					decl tmp4        = (meanFORECAST_ORG_frcst[i]  );        //meanFORECAST_ORG[j] = (  ( meanr(FORECAST_ORG[j])  )[index].*mY_stddev[j]) + mY_mean[j];
		
					tmp1 = tmp1[Start_t0:];
		
					tmp4 = tmp4[index|now_index];
					tmp4 = tmp4[Start_t0:];
		
					if(StDev_in_Standardization == 0)	{ tmp4 = tmp4              + mY_mean[i];}
					else		                    	{ tmp4 = tmp4*mY_stddev[i] + mY_mean[i];}
			
				    if(i==0)
				    {
				  	  excelfile_nowcast_ns[][0]    = tmp1;
					  excelfile_nowcast_ns[][kk+1] = tmp4;	
						  for(decl k=0; k<hrzn; k++)
						  {	(exf_now_ns_fill[k])	[kk]	= tmp4[ rows(tmp4)-1-(hrzn-1-k) ];	  } // nowcast& forecast values
				     }
				}
		
/****************************************************************** OUT-OF-SAMPLE ANALYSIS *************************************************************************************************************/
// 				index_pr 	 	= index|(now_index-1);
 				index_pr 	 	= index|(now_index);

				decl meanVAR_GDP_T_MM_ind   = meanVAR_GDP_T_MM[index_pr];
				decl meanSTDEV_GDP_T_MM_ind = meanSTDEV_GDP_T_MM[index_pr];				  decl Tttmp = sizer(meanSTDEV_GDP_T_MM_ind);
//		   		println("%c", {"GDP vol_t","GDP Var_t","Fac vol_t","Fac Var_t"}, "%r", sdates[Tttmp-8:], "%10.3f",  (meanSTDEV_GDP_T_MM_ind~meanVAR_GDP_T_MM_ind~meanSTDEV_FACTOR_T_MM[index_pr]~meanVAR_FACTOR_T_MM[index_pr])[Tttmp-8:][]);
		   		println("%c", {"GDP vol_t","GDP Var_t","Fac vol_t","Fac Var_t"}, "%r", sdates[], "%10.3f",  (meanSTDEV_GDP_T_MM_ind~meanVAR_GDP_T_MM_ind~meanSTDEV_FACTOR_T_MM[index_pr]~meanVAR_FACTOR_T_MM[index_pr])[][]);
//		   		println({"Factor volatility"},"%c", {"StDev_t","Var_t"}, "%r", sdates, "%10.3f",  meanSTDEV_FACTOR_T_MM[index_pr]~meanVAR_FACTOR_T_MM[index_pr]);															 )

				if(SV_gdp ==1)
				{
					if(draworder==1){	DrawTMatrix(0,  (meanVAR_GDP_T_MM_ind')     , {"VAR_"} , dSTARTYEAR, dSTARTMONTH  ,freq/3, 0,2);   }
					ShowDrawWindow();
					if(draworder==1){   DrawTMatrix(0,   sqrt(meanVAR_GDP_T_MM')    , {"STD_"} , dSTARTYEAR, dSTARTMONTH  ,freq/3, 0,2);   }
					ShowDrawWindow();
				}
				
				decl veccind2 = vecindex(meanht_GDP_MM .!= 0);
				decl meanht_GDP_MM_ind = meanht_GDP_MM[veccind2];
				
				decl veccind3 = vecindex(meanht_GDPT_MM .!= 0);
				decl meanht_GDPT_MM_ind = meanht_GDPT_MM[veccind3];
				
				decl varr_band = zeros(rows(VAR_GDP_T_MM), 4);

				decl stddev_ = moments(VAR_GDP_T_MM')[2][];
	 				 stddev_ = stddev_'	;	  //				println(stddev_);
				varr_band[][2] = meanr(VAR_GDP_T_MM);
				varr_band[][1] = varr_band[][2] - 1.04.*stddev_;
				varr_band[][3] = varr_band[][2] + 1.04.*stddev_;
				varr_band[][0] = stddev_;
//				savemat("varr_band.xlsx", varr_band);

/********************************************************** GDP and QUARTERLY FACTOR ********************************************************************************************************************/
				decl mpred = FORECAST_ORG_frcst[0][index_pr][];
				decl yy_pred = meanr(mpred); //(yy_forecast')[][0];	  // println(index_pr);
//				println("here ", sortr(mpred));
//				decl yy_pred_lb = yy_pred - 1.96*sqrt(varr(mpred)); //(yy_forecast')[][0];	  // println(index_pr);
//				decl yy_pred_ub = yy_pred + 1.96*sqrt(varr(mpred)); //(yy_forecast')[][0];	  // println(index_pr);
				
				if(StDev_in_Standardization == 0) {	yy_pred = yy_pred               + mY_mean[0];	   }
				else							  {	yy_pred = yy_pred.*mY_stddev[0] + mY_mean[0];	   }	   

				decl yy_pred_lb = sortr(mpred)[][round(0.05*sizec(mpred))]; //(yy_forecast')[][0];	  // println(index_pr);
				decl yy_pred_ub = sortr(mpred)[][round(0.95*sizec(mpred))]; //(yy_forecast')[][0];	  // println(index_pr);
				if(StDev_in_Standardization == 0) {	yy_pred_lb = yy_pred_lb               + mY_mean[0];	   }
				else							  {	yy_pred_lb = yy_pred_lb.*mY_stddev[0] + mY_mean[0];	   }
				if(StDev_in_Standardization == 0) {	yy_pred_ub = yy_pred_ub               + mY_mean[0];	   }
				else							  {	yy_pred_ub = yy_pred_ub.*mY_stddev[0] + mY_mean[0];	   }					

				
//				println("%c", {"Nowcasted GDP, GDP"}, "%r", sdates[], "%10.3f",  (yy_pred~((yy1_gro[][0])[aIndex[0]]))[][] );
               decl realGDPgr =  yy1_gro[aIndex[0]][0];
				println("%c", {"LB", "UB", "Nowcasted GDP, GDP"}, "%r", sdates[], "%10.3f",  realGDPgr~yy_pred[1:]~yy_pred_ub[1:]~yy_pred_lb[1:] );
//				println("%c", {"Nowcasted GDP, GDP"}, "%r", sdates[Tttmp-8:], "%10.3f",  (yy_pred~((yy1_gro[][0])[aIndex[0]]))[Tttmp-8:][] );
/********************************************************** GDP and QUARTERLY FACTOR ********************************************************************************************************************/

				decl fac_q = (meanBtTMM[0])[aIndex[0]];
				decl fac_m = (meanBtTMM[2]);
				
				decl out_table1 	= table(LAMBDAFMM')		;
				decl out_table1SDev = table(LAMBDAFMMst')	;
				decl out_table2 	= table(SIG2YMM')		;
				decl out_table3 	= table(PHIMM'~SIG2_FACVOL'~SIG2_GDPVOL')		;
//				decl out_table3 	= table(PHIMM');
				
//				DrawDensity(1, (LAMBDAFMM[0][])  , "var", TRUE, TRUE, TRUE);
//				ShowDrawWindow();
				
//				println("%c", {"f1 Load*SDev", "std dev."}, "%r" , data_name[selection_name], "%10.4f", out_table1SDev);		
				println("%c", {"f1 Load"     , "std dev."}, "%r" , data_name[selection_], "%10.4f", out_table1);
//				println("%c", {"\sigma^2_u"  , "std dev."}, "%r" , data_name[selection_], "%10.4f", out_table2);
				println("%c", {"mean","std dev."}, "%r", {"Phi","sigma^2_facvol","sigma^2_gdpvol"}, "%10.4f", out_table3);

				if(StDev_in_Standardization == 0)
					{
//						(FORECAST_ORG_frcst[0])[index_pr][]		  + mY_mean[0];
						densh0 = LLIKE_PRDENS_MM[0]               + mY_mean[0];
						densh1 = LLIKE_PRDENS_MM[1]               + mY_mean[0];
						densh2 = LLIKE_PRDENS_MM[2]               + mY_mean[0];
						densh3 = LLIKE_PRDENS_MM[3]               + mY_mean[0];
						densh4 = LLIKE_PRDENS_MM[4]               + mY_mean[0]; 
					}
				else
					{
						densh0 = LLIKE_PRDENS_MM[0].*mY_stddev[0] + mY_mean[0];
						densh1 = LLIKE_PRDENS_MM[1].*mY_stddev[0] + mY_mean[0];
						densh2 = LLIKE_PRDENS_MM[2].*mY_stddev[0] + mY_mean[0];
						densh3 = LLIKE_PRDENS_MM[3].*mY_stddev[0] + mY_mean[0];
						densh4 = LLIKE_PRDENS_MM[4].*mY_stddev[0] + mY_mean[0];
					}

			mdensh0[kk][] = densh0;					// println(densh0);
			mdensh1[kk][] = densh1;
			mdensh2[kk][] = densh2;
			mdensh3[kk][] = densh3;
			mdensh4[kk][] = densh4;

			mPLh0[kk][] = LLIKE_PR_MM[0];
			mPLh1[kk][] = LLIKE_PR_MM[1];
			mPLh2[kk][] = LLIKE_PR_MM[2];
			mPLh3[kk][] = LLIKE_PR_MM[3];
			mPLh4[kk][] = LLIKE_PR_MM[4];

//			savemat("Model"+ModelNo+"Density_h0_"+Year+"_"+Month+"_.xlsx", mdensh0' );
//			savemat("Model"+ModelNo+"Density_h1_"+Year+"_"+Month+"_.xlsx", mdensh1' );
//			savemat("Model"+ModelNo+"Density_h2_"+Year+"_"+Month+"_.xlsx", mdensh2' );
//			savemat("Model"+ModelNo+"Density_h3_"+Year+"_"+Month+"_.xlsx", mdensh3' );
//			savemat("Model"+ModelNo+"Density_h4_"+Year+"_"+Month+"_.xlsx", mdensh4' );
//			
////			savemat("Model"+ModelNo+"PL_h0_"+Year+"_"+Month+"_.xlsx", mPLh0' );
////			savemat("Model"+ModelNo+"PL_h1_"+Year+"_"+Month+"_.xlsx", mPLh1' );
////			savemat("Model"+ModelNo+"PL_h2_"+Year+"_"+Month+"_.xlsx", mPLh2' );
////			savemat("Model"+ModelNo+"PL_h3_"+Year+"_"+Month+"_.xlsx", mPLh3' );
////			savemat("Model"+ModelNo+"PL_h4_"+Year+"_"+Month+"_.xlsx", mPLh4' );
//


	}// for(kk = start2; kk < kkend+1 ; kk++)
													

}
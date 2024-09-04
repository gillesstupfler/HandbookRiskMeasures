#-------------------------------------------------------------------------#
#
#         Risk measures beyond quantiles
#         
#      by Abdelaati Daouia and Gilles Stupfler 
#             Updated: September 4, 2024 
#  
#-------------------------------------------------------------------------#

# NOTE: This code is not run time optimized. Problems have not appeared so far, 
#       but their absence cannot be guaranteed for.


#Content:    PACKAGES REQUIRED 
#            INTERNAL FUNCTIONS
#            FIGURE 1.1 (A)-(B)-(C)
#            FIGURE 1.2 (A)
#            FIGURE 1.1 (D)-(E)-(F)
#            FIGURE 1.2 (B)
#            FIGURE 1.1 (G)-(H)-(I)
#            FIGURE 1.2 (C)
#            FIGURE 1.2 (D)
#            FIGURE 1.3
#            FIGURE 1.6  
#            FIGURE 1.4
#            FIGURE 1.5
#            FIGURE 1.8
#            TABLE 1.1
#            FIGURE 1.9
#            FIGURE 1.7
#            FIGURE 1.10

# Clear the working space:         
rm(list = ls())

################################################################################
###
### REQUIRED PACKAGES
###
################################################################################

#install.packages("extRemes")
library(extRemes)
library(evt0)
library(tea)
# library(devtools)
# install_github("https://github.com/AntoineUC/Expectrem.git")
library(Expectrem)
require("expectreg") 
#
# library(ggpubr)
library(ggplot2)
# library(tidyr)
# library(dplyr)

################################################################################
###
### INTERNAL FUNCTIONS
###
################################################################################

#-------------------------------------------------------------------------------
###
### Estimation of the tail index gamma (xi in the manuscript) using the Moment 
### Estimator for time series and iid observations
###
###
#-------------------------------------------------------------------------------
MomTailIndex <- function(data, k, tau1=NULL){
  # initialization
  QHat <- NULL
  # main body:
  if(is.null(k)) stop("Enter a value for the parameter 'k' ")
  # sample size
  ndata <- length(data)
  # derives the ordered data
  dataord <- sort(data, decreasing=TRUE)
  # computes the peaks above a threshold
  z <- log(dataord[1:k]) - log(dataord[k+1])
  # set the large threshold
  muHat <- dataord[k+1]
  # compute the moments
  M1 <- mean(z)
  M2 <- mean(z^2)
  # compute the negative gamma
  gammaN <- 1 - 0.5/(1 - M1^2 / M2)
  # compute the tail index estimate by the moment-based method
  gammaHat <- M1 + gammaN
  # compute the scaling norming sequence
  sigmaHat <- muHat * M1 * (1 - gammaN)
  # compute an estimate of the extreme quantile
  if(!is.null(tau1)){
    QHat <- muHat + sigmaHat * ((ndata*(1-tau1)/k)^(-gammaHat) - 1) / gammaHat
  }
  return(list(gammaHat=gammaHat,
              gammaNHat=gammaN,
              muHat = muHat,
              sigmaHat = sigmaHat,
              QHat=QHat))
}
#-------------------------------------------------------------------------------

#-------------------------------------------------------------------------------
###
### Estimation of the tail index gamma using the Maximum Lilelihood (ML)
### estimator, for time series and iid observations
###
###
#-------------------------------------------------------------------------------
MLTailIndex <- function(data, k, var=FALSE, varType="asym-Dep", tau1=NULL,
                        bigBlock=NULL, smallBlock=NULL, alpha=0.05, start=NULL){
  # initialization
  QHat <- NULL
  VarGamHat <- NULL
  CIgamHat <- NULL
  
  # main body:
  if(is.null(k)) stop("Enter a value for the parameter 'k' ")
  if(!any(varType=="asym-Dep", varType=="asym-Ind")) stop("The parameter 'varType' can only be 'asym-Dep' or 'asym-Ind' ")
  if(any(is.null(start), is.na(start))) {
    start <- c(sqrt(6 * var(data)) / pi, 1e-8)
  }
  # compute the sample size
  ndata <- length(data)
  # derives the ordered data
  dataord <- sort(data, decreasing=TRUE)
  muHat <- dataord[k+1]
  z <- data[data>muHat] - muHat
  # #  
  est <- extRemes::fevd(data, threshold = muHat, type="GP", method = "MLE")$results$par
  sigmaHat <- as.numeric(est[1])
  gammaHat <- as.numeric(est[2])
  # compute an estimate of the extreme quantile
  if(!is.null(tau1)){
    QHat <- muHat + sigmaHat * ((ndata*(1-tau1)/k)^(-gammaHat) - 1) / gammaHat
  }
  # compute the ML estimator variance (for iid and time series data)
  if(var){
    AdjVar <- 1
    if(varType=="asym-Dep"){
      t <- as.numeric(quantile(data, 1-k/ndata))
      sizeBlock <- bigBlock+smallBlock
      indx <- seq(1, ndata, by=sizeBlock)[1:floor(ndata/sizeBlock)]
      indx <- array(indx, c(length(indx),1))
      sexc <- apply(indx, 1, numexceed, data=data, t=t, rn=bigBlock)
      AdjVar <- ndata/(bigBlock*k) * var(sexc)
    }
    # computes the asymptotic variance
    VarGamHat <- (1+gammaHat)^2 * AdjVar
    # computes the margin error
    ME <- sqrt(VarGamHat)*qnorm(1-alpha/2) / sqrt(k)
    # defines an approximate (1-alpha)100% confidence interval for the tail index
    CIgamHat <- c(gammaHat-ME, gammaHat+ME)
    return(list(gammaHat=gammaHat,
                VarGamHat=VarGamHat,
                CIgamHat=CIgamHat,
                muHat = muHat,
                sigmaHat = sigmaHat,
                QHat=QHat))
  }
  return(list(gammaHat=gammaHat,
              muHat = muHat,
              sigmaHat = sigmaHat,
              QHat=QHat))
}
#-------------------------------------------------------------------------------


#-------------------------------------------------------------------------------
###
### Test of Thm 5.2.12 for tail-heaviness
###  (In order to check the extreme value condition of tail-heaviness, 
###  we used the test of Theorem~5.2.12 pp.172-173 in~\cite{deHaanFeri}).
### 
#-------------------------------------------------------------------------------
Tail_Heaviness_Test <- function(data, kmax=200){
  # inputs: 
  # data = sample
  # kmax = maximal value of k (typically kmax = n-1)
  # output : vector "pval" of p-values to be plotted as a function of kk=1:kmax
  #          Decision : reject the tail-heaviness of the data if pval < 0.05
  S=rep(0,kmax)
  pval=rep(0,kmax)
  ################### Limit distribution #################
  ds=0.001
  saxe=seq(0,1,ds)
  N=10000
  I=rep(0,N)
  i=1
  while(i<=N){
    B=c(0,cumsum(rnorm(length(saxe)-1,0,sqrt(ds))))
    A=sum((B[-1]/saxe[-1]-B[length(B)]))*ds
    I[i]=sum((B[-1]/saxe[-1]-B[length(B)]+log(saxe[-1])*A)^2*saxe[-1]^2)*ds
    #print(i*100/N)
    i=i+1
  }
  X=data   
  n=length(X)
  k=1
  while(k<=kmax){
    kn=k
    gammahat=mop(X,p=0,k=kn,method="MOP")$EVI
    Skn=sum((log(quantile(X,1-(1:(kn-1))/n,type=1)/quantile(X,1-kn/n,type=1)[1])/gammahat[1]+log((1:(kn-1))/kn))^2*((1:(kn-1))/kn)^2)/kn
    S[k]=Skn
    pval[k]=mean(kn*Skn<I)
    k=k+1
  }
  kk=1:kmax
  return(list(pval=pval,kk=kk))
}
#-------------------------------------------------------------------------------


#-------------------------------------------------------------------------------
###
### Ordinary ALS extremile estimator
### 
#-------------------------------------------------------------------------------
### internal functions
.sg <- function(gam)
{
  #input: gam = extremile order in (0,1)
  #output: power $s(gam)$ in the definition of the measure $K_{gam}$
  log(1/2)/log(1-gam)
}
# _________________________________

.Kg <- function(gam, t)
{
  #input: gam = extremile order in (0,1)
  #         t = real number in the support [0,1] of the $K_{gam}$
  #output: measure $K_{gam}(t)$ 
  ((1-(1-t)^(.sg(gam)))*(0<gam)*(gam<=0.5))+((t^(.sg(1-gam)))*(0.5<gam)*(gam<1))
}
# _________________________________

#An alternative : 
.Jg <- function(gam, t)
{
  #input: gam = extremile order in (0,1)
  #         t = real number in the support (0,1] of the density $J_{gam}=K'_{gam}$
  #output: weight-generating function $J_{gam}(t)$ 
  #
  if ((0<gam) & (gam<=0.5))
  {
    res = (.sg(gam))*(1-t)^(.sg(gam)-1)
  }
  else if  ((0.5<gam) & (gam<1)) 
  {
    res = (.sg(1-gam))*t^(.sg(1-gam)-1)
  }
  return(res)
  #((.sg(gam)*(1-t)^(.sg(gam)-1))*(0<gam)*(gam<=0.5))+((.sg(1-gam)*t^(.sg(1-gam)-1))*(0.5<gam)*(gam<1))
}

### main functions
empirical_extremile <- function(ytab, gam)
{
  #inputs:
  #    ytab = sample of nx1 obs
  #    gam = extremile order in (0,1)
  #output: Ordinary $gam$th sample extremile $\widehat\xi_{gam}$.
  #__________________________________
  sytab=sort(ytab)
  n=length(ytab)
  compute<-function(gam, x)
  {res=0
  for (i in 1:n)
  {res = res + ((.Kg(gam,i/n)-.Kg(gam,(i-1)/n))*x[i])}
  return(res)
  }
  return(unlist(lapply(gam,compute,sytab)))
}
###

als_extremile <- function(data,tau)
{
  #inputs:
  #       data = sample of nx1 obs
  #        tau = order tau in (0,1)
  #output: res = Ordinary $tau$th sample ALS estimator $\widetilde\xi_{tau}$.
  #$$ \widetilde{\xi}_{\tauma} = 
  # \sum_{i=1}^n  J_{tau}(i/n) * Ysort[i]  / \sum_{i=1}^n  J_{tau}(i/n) $$
  #
  # return(num/den)
  sdata=sort(data)
  oneses=(0*sdata) + 1
  #internal function ---
  compute<-function(gam, x)
  {
    res=0
    n=length(x)
    for (i in 1:n)
    {
      res = res + ((.Jg(gam,i/n))*x[i])
     }
    return(res)
  }
  #----------------------
  ntau <- length(tau)
  res <- 0 * tau
  for (i in 1:ntau)
  { 
    num <- compute(tau[i], sdata) #unlist(lapply(tau[i],compute,sdata))
    den <- compute(tau[i], oneses) #unlist(lapply(tau[i],compute,oneses))
    res[i] <- num/den
  }
  return(res)
}
#-------------------------------------------------------------------------------


#-------------------------------------------------------------------------------
###
### Ordinary sample ES
### 
#-------------------------------------------------------------------------------
expected_shortfall<- function(data,tau)
{
  #inputs:
  #       data = sample of nx1 obs
  #        tau = order tau in (0,1)
  #output: res = $tau$th sample ES estimator $\widehat\textrm{ES}_{tau}$.
  #__________________________________
  ntau <- length(tau)
  res <- 0 * tau
  for (i in 1:ntau)
  { 
    quant <- quantile(data, probs = tau[i], type = 1)
    #res[i] <- mean((data > quant)*data)/(1-tau[i])
    res[i] <- mean((data >= quant)*data)/mean((data >= quant))
  }
  return(res)
 }
#-------------------------------------------------------------------------------


#-------------------------------------------------------------------------------
###
### Extrapolated QES and XES estimators
### 
#-------------------------------------------------------------------------------
  #________________________________
  # internal function 
  # Hill or BR-Hill estimator 
  #________________________________
  Hill_br  <- function(data, k) {
    # OUTPUT : classical Hill estimator or its bias-reduced version (choose below)
    # BR-HILL
    mop(data, k, p=0, "RBMOP")$EVI
  }

#________________________________
# internal function 
# Hill or BR-Hill estimator 
#________________________________
Hill  <- function(data, k) {
  # OUTPUT : classical Hill estimator or its bias-reduced version (choose below)
  # BR-HILL
  mop(data, k, p=0, "RBMOP")$EVI
}
  
  #____________________________________________________________________
  # internal function 
  # Weissman quantile estimator $\widehat{q}_{\tau'_n}^{\star}$
  #____________________________________________________________________
  weissman_quantile <- function(ytab, k, taunp)
  {
    #inputs:
    #       ytab = sample of nx1 obs
    #       taunp = \tau'_n #(e.g. 1-1/n)
    #         k  = sample fraction varying from "1" up to "n-1"
    #output: res = \widehat{q}_{\tau'_n}^{\star}.
    n=length(ytab)
    ysort=sort(ytab) 
    #Hill:
    gam <- Hill_br(ytab, k)
    #\widehat{q}_{\tau'_n}^{\star}:      
    ysort[n-k] * (k/(n*(1-taunp)))^(gam)
  }


#____________________________________________________________________
# internal function (extrapolated indirect XES)
# \widetilde{\textrm{XES}}^{\star}_{\tau'_n}
#____________________________________________________________________
XES_tilde_star_indirect <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  n <- length(ytab)
  ysort <- sort(ytab) 
  hill <- Hill_br(ytab, k)
  ( (1-taunp)/(k/n) )^(-hill) * ( (hill)^(-1) - 1)^(- hill) * ysort[n-k]/(1-hill)   
}

  #____________________________________________________________________
  # internal function (sample direct XES)
  # \widehat{\textrm{XES}}_{\tau} := \frac{1}{1-{\tau}} \int_{{\tau}}^1 \widehat{\xi}_{t} dt
  #____________________________________________________________________
  XES_hat_direct <- function(ytab, tau){
    n <- length(ytab) 	
    #
    integral <- function(ytab, ttau)
    { 
      integ_fun <- function(t) expectreg::expectile(ytab, probs = t)
      integrate(integ_fun, ttau, 1, rel.tol = .Machine$double.eps^0.2)$value 
    }    
    #
    ntau <- length(tau)
    res <- 0 * tau
    for (i in 1:ntau)
      { 
      res[i] <- integral(ytab=ytab, ttau=tau[i])/(1-tau[i])
      }
    return(res)    
   }

#____________________________________________________________________
# internal function (extrapolated direct XES)
# \widehat{\textrm{XES}}^{\star}_{\tau'_n}
#____________________________________________________________________
XES_hat_star_direct <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  n <- length(ytab) 	
  #
  integral <- function(ytab, k)
  { integ_fun <- function(t) expectreg::expectile(ytab, probs = t)
  integrate(integ_fun, (1-k/n), 1, rel.tol = .Machine$double.eps^0.2)$value 
  }      
  #\widehat{\textrm{XES}}_{\tau_n} := \frac{1}{1-{\tau_n}} \int_{{\tau_n}}^1 \widehat{\xi}_{t} dt
  XES_taun <- (n/k) * integral(ytab=ytab, k=k)
  hill <- Hill_br(ytab, k)
  #res 
  ( (1-taunp)/(k/n) )^(-hill) * XES_taun   
}

#____________________________________________________________________
# internal function (extrapolated direct QES)
# \widehat{\textrm{ES}}^{\star}_{\tau'_n}
#____________________________________________________________________
QES_hat_star_direct <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  n <- length(ytab) 	
  #\widehat{\textrm{ES}}_{\tau_n} := \frac{1}{1-{\tau_n}} \int_{{\tau_n}}^1 \widehat{q}_{t} dt
  QES_taun <- expected_shortfall(ytab, 1-(k/n))
  hill <- Hill_br(ytab, k)
  #res 
  ( (1-taunp)/(k/n) )^(-hill) * QES_taun   
}

#____________________________________________________________________
# internal function (extrapolated indirect QES)
# \widetilde{\textrm{XES}}^{\star}_{\tau'_n}
#____________________________________________________________________
QES_tilde_star_indirect <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  n <- length(ytab)
  ysort <- sort(ytab)
  hill <- Hill_br(ytab, k)
  #\widetilde{\textrm{ES}}_{\tau_n} := \widehat{q}{\tau_n} / (1-\widehat{\gamma}_{\tau_n})
  QES_taun <- ysort[n-k]/(1-hill)
  #res 
  ( (1-taunp)/(k/n) )^(-hill) * QES_taun   
}

#____________________________________________________________________
# internal function 
# Weissman quantile estimator $\widehat{q}_{\tau'_n}^{\star}$
#____________________________________________________________________
weissman_quantile <- function(ytab, k, taunp)
{
  #inputs:
  #       ytab = sample of nx1 obs
  #       taunp = \tau'_n #(e.g. 1-1/n)
  #         k  = sample fraction varying from "1" up to "n-1"
  #output: res = \widehat{q}_{\tau'_n}^{\star}.
  n=length(ytab)
  ysort=sort(ytab) 
  #Hill:
  gam <- Hill_br(ytab, k)
  #\widehat{q}_{\tau'_n}^{\star}:      
  ysort[n-k] * (k/(n*(1-taunp)))^(gam)
}

#-------------------------------------------------------------------------------
###
### Extrapolated extremile estimators
### 
#-------------------------------------------------------------------------------
  #____________________________________________________________________
  # internal function (extrapolated direct xtremile)
  # \widehat{x}^{\star}_{\tau'_n}
  #____________________________________________________________________
  xtremile_hat_star_direct <- function(ytab, k, taunp){
    #taunp  <- \tau'_n 
    n <- length(ytab) 	
    hill <- Hill_br(ytab, k)
    #res 
    ( (1-taunp)/(k/n) )^(-hill) * als_extremile(ytab, 1-k/n)  
  }

#____________________________________________________________________
# internal function (extrapolated indirect xtremile)
# \widetilde{x}^{\star}_{\tau'_n}
#____________________________________________________________________
xtremile_tilde_star_indirect <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  hill <- Hill_br(ytab, k)
  #res 
  gamma(1-hill) * (log(2))^(hill) * weissman_quantile(ytab, k, taunp)  
}

  
################################################################################
###
### Extrapolated expectile estimators
### 
################################################################################

  #____________________________________________________________________
  # internal function (extrapolated direct xpectile)
  # \widehat{e}^{\star}_{\tau'_n}
  #____________________________________________________________________
  xpectile_hat_star_direct <- function(ytab, k, taunp){
    #taunp  <- \tau'_n 
    n <- length(ytab) 	
    hill <- Hill_br(ytab, k)
    #res 
    ( (1-taunp)/(k/n) )^(-hill) *  expectreg::expectile(ytab, probs = 1-k/n)
  }

#____________________________________________________________________
# internal function (extrapolated indirect xpectile)
# \widetilde{e}^{\star}_{\tau'_n}
#____________________________________________________________________
xpectile_tilde_star_indirect <- function(ytab, k, taunp){
  #taunp  <- \tau'_n 
  hill <- Hill_br(ytab, k)
  #res 
  ((hill)^(-1) - 1)^(-hill) * weissman_quantile(ytab, k, taunp)  
}

#-------------------------------------------------------------------------------
###
### Extrapolated expectile BR-estimators
### 
#-------------------------------------------------------------------------------
CIextExpect=function(X, k = trunc(length(X)/10), tau, method = "direct",ci.level=0.95) 
{
  n = length(X)
  mopest = mop(X, 1:(n - 1), 0, method = "RBMOP")
  if (length(k) > 1) {
    stop("k must be of length 1.")
  }
  if (length(tau) > 1) {
    stop("tau must be of length 1.")
  }
  if (k > n - 1 || k < 1) {
    stop("k must be between 1 and n-1.")
  }
  if (method != "direct" && method != "indirect" && method != "direct_naive" && method != "indirect_naive" && method != "direct_PS" && method != "indirect_PS") {
    stop("method may be either direct or indirect.")
  }
  
  if (method == "direct_naive") {
    
    qtp = expect(X, 1 - k/n)
    gammahat=tindexp(X,k,br=T)
    if(gammahat>0.5){
      print("WARNING : Tail index above 1/2 ! Use the indirect method rather ?")
    }
    r = (1 - mean(X)/qtp) * (n/(n - 2 * k)) * (1 + mopest$beta * 
                                                 gammahat * Fbar(X, qtp)^(-mopest$rho)/(gammahat * (1 - 
                                                                                                      mopest$rho - gammahat)))^(-1)
    rbet = (1 - mean(X)/(qtp * (k/(n * (1 - tau)))^(gammahat))) * 
      (1/(2 * tau - 1)) * (1 + mopest$beta * gammahat * (1/gammahat - 
                                                           1)^(-mopest$rho) * (1 - tau)^(-mopest$rho)/(gammahat * 
                                                                                                         (1 - mopest$rho - gammahat)))^(-1)
    estimpoint=qtp * (k/(n * (1 - tau)))^gammahat * (1 + ((k/(n * 
                                                                (1 - tau)))^mopest$rho - 1)/mopest$rho * mopest$beta * 
                                                       gammahat * (n/k)^mopest$rho) * (r/rbet)^gammahat * 
      (1 + ((1/gammahat - 1)^(-mopest$rho) * rbet^(-mopest$rho) - 
              1)/mopest$rho * mopest$beta * gammahat * (1 - 
                                                          tau)^(-mopest$rho))/(1 + ((1/gammahat - 1)^(-mopest$rho) * 
                                                                                      r^(-mopest$rho) - 1)/mopest$rho * mopest$beta * gammahat * 
                                                                                 (k/n)^(-mopest$rho))
    
    varnaive=gammahat^3*(1-gammahat)/(1-2*gammahat)
    
    estimup=estimpoint*exp(-(sqrt(varnaive)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1-ci.level)/2)))
    
    estimdown=estimpoint*exp(-(sqrt(varnaive)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1+ci.level)/2)))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint,Upper_bound=estimup))
  }
  
  if (method == "indirect_naive") {
    
    gammahat=mopest$EVI[k]
    if(gammahat>1){
      stop("Tail index greater than 1 ! Expectile does probably not exist !")
    }
    qtp = quantile(X, 1 - k/n)*(1/gammahat-1)^(-gammahat)
    r = (1 - mean(X)/qtp) * (n/(n - 2 * k)) * (1 + mopest$beta * 
                                                 gammahat * Fbar(X, qtp)^(-mopest$rho)/(gammahat * (1 - 
                                                                                                      mopest$rho - gammahat)))^(-1)
    rbet = (1 - mean(X)/(qtp * (k/(n * (1 - tau)))^(gammahat))) * 
      (1/(2 * tau - 1)) * (1 + mopest$beta * gammahat * (1/gammahat - 
                                                           1)^(-mopest$rho) * (1 - tau)^(-mopest$rho)/(gammahat * 
                                                                                                         (1 - mopest$rho - gammahat)))^(-1)
    estimpoint=(1/gammahat - 1)^(-gammahat) * quantile(X, 1 - 
                                                         k/n) * (k/(n * (1 - tau)))^gammahat * (1 + ((k/(n * 
                                                                                                           (1 - tau)))^mopest$rho - 1)/mopest$rho * mopest$beta * 
                                                                                                  gammahat * (n/k)^mopest$rho) * (1 + ((1/gammahat - 
                                                                                                                                          1)^(-mopest$rho) * rbet^(-mopest$rho) - 1)/mopest$rho * 
                                                                                                                                    mopest$beta * gammahat * (1 - tau)^(-mopest$rho))/(rbet^gammahat)
    varnaive=gammahat^2
    
    estimup=estimpoint*exp(-(sqrt(varnaive)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1-ci.level)/2)))
    
    estimdown=estimpoint*exp(-(sqrt(varnaive)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1+ci.level)/2)))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint,Upper_bound=estimup))
    
  }
  
  if (method == "direct_PS") {
    
    gammahat=mop(X,k=k,p=0,method="MOP")$EVI
    
    Fbarhat=mean(X>expect(X,1-k/n))
    
    biasPS=-gammahat*(1/gammahat-1)^gammahat*mean(X)*sqrt(k)/quantile(X,1-k/n)
    
    varPS=gammahat^2+2*gammahat^3*(1/gammahat-1)^gammahat/((1-gammahat)^2*log((k/n)/(1-tau)))+gammahat^2/((1-2*gammahat)*log((k/n)/(1-tau))^2)*(1+Fbarhat/(k/n))/(1+(1-2*k/n)*Fbarhat/(k/n))^2
    
    estimpoint=extExpect(X,k=k,tau=tau,method = "direct",br=F,estim="Hill")
    
    estimup=estimpoint*exp(biasPS/sqrt(k)+log((k/n)/(1-tau))/sqrt(k)*sqrt(varPS)*qnorm((1+ci.level)/2))
    
    estimdown=estimpoint*exp(biasPS/sqrt(k)-log((k/n)/(1-tau))/sqrt(k)*sqrt(varPS)*qnorm((1+ci.level)/2))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint*exp(biasPS/sqrt(k)),Upper_bound=estimup))
  }
  
  if (method == "indirect_PS") {
    
    gammahat=mop(X,k=k,p=0,method="MOP")$EVI
    
    varPS=gammahat^2/log(k/(n*(1-tau)))^2*(1+(1/(1-gammahat)-log(1/gammahat-1)+log(k/(n*(1-tau))))^2)
    
    estimpoint=extExpect(X,k=k,tau=tau,method = "indirect",br=F,estim="Hill")
    
    estimup=estimpoint*exp(-(sqrt(varPS)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1-ci.level)/2)))
    
    estimdown=estimpoint*exp(-(sqrt(varPS)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1+ci.level)/2)))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint,Upper_bound=estimup))
    
  }
  
  if (method == "direct") {
    qtp = expect(X, 1 - k/n)
    gammahat=tindexp(X,k,br=T)
    if(gammahat>0.5){
      print("WARNING : Tail index above 1/2 ! Use the indirect method rather ?")
    }
    r = (1 - mean(X)/qtp) * (n/(n - 2 * k)) * (1 + mopest$beta * 
                                                 gammahat * Fbar(X, qtp)^(-mopest$rho)/(gammahat * (1 - 
                                                                                                      mopest$rho - gammahat)))^(-1)
    rbet = (1 - mean(X)/(qtp * (k/(n * (1 - tau)))^(gammahat))) * 
      (1/(2 * tau - 1)) * (1 + mopest$beta * gammahat * (1/gammahat - 
                                                           1)^(-mopest$rho) * (1 - tau)^(-mopest$rho)/(gammahat * 
                                                                                                         (1 - mopest$rho - gammahat)))^(-1)
    estimpoint=qtp * (k/(n * (1 - tau)))^gammahat * (1 + ((k/(n * 
                                                                (1 - tau)))^mopest$rho - 1)/mopest$rho * mopest$beta * 
                                                       gammahat * (n/k)^mopest$rho) * (r/rbet)^gammahat * 
      (1 + ((1/gammahat - 1)^(-mopest$rho) * rbet^(-mopest$rho) - 
              1)/mopest$rho * mopest$beta * gammahat * (1 - 
                                                          tau)^(-mopest$rho))/(1 + ((1/gammahat - 1)^(-mopest$rho) * 
                                                                                      r^(-mopest$rho) - 1)/mopest$rho * mopest$beta * gammahat * 
                                                                                 (k/n)^(-mopest$rho))
    psihat=mean((X-qtp)*(X>qtp))
    
    Fbarhat=mean(X>qtp)
    
    psi2hat=min(max(2*Fbarhat*qtp^2*gammahat^2*(1/abs((1-gammahat)*(1-2*gammahat))+Fbarhat^(-mopest$rho)*mopest$beta/mopest$rho*( 1/abs((1-gammahat-mopest$rho)*(1-2*gammahat-mopest$rho)) - 1/abs((1-gammahat)*(1-2*gammahat)) )), psihat^2),sqrt(mean((X-qtp)^4*(X>qtp))))
    
    mhat=mean(X)
    
    alphan=1-Fbarhat
    
    M11phi=k/n*(psi2hat/psihat^2-1)
    
    M12phi=k/n*alphan/(1-alphan)
    
    M22phi=k/n*alphan/(1-alphan)
    
    M11xi=(psihat/qtp)^2*((qtp-mhat)^2*M11phi)/(psihat+Fbarhat*(qtp-mhat))^2
    
    M12xi=gammahat*psihat/qtp*((qtp-mhat)*M12phi)/(psihat+Fbarhat*(qtp-mhat))
    
    M22xi=gammahat^2*M22phi
    
    epsilon=(1/gammahat-1)^(-gammahat)*(1-mhat/qtp)^(-gammahat)*(1-2*k/n)^gammahat*(Fbarhat/(k/n))^gammahat
    
    M11=1/gammahat^2*(epsilon^2*(Fbarhat/(k/n))^2*M11xi-2*epsilon*(Fbarhat/(k/n))*M12xi+M22xi)
    
    M12=1/gammahat*(M12xi-epsilon*(Fbarhat/(k/n))*M11xi)
    
    M22=M11xi
    
    S11=M11*1/(1+Fbarhat/(k/n))^4*(1+8*M11*(1+Fbarhat/(k/n))^(-2)/(k)) #order 2
    
    S12=-1/(1+Fbarhat/(k/n))^2*M12*(1+3*M11*(1+Fbarhat/(k/n))^(-2)/k) #order 2
    
    S22=M22  
    
    nablah1=qtp*(1-2*k/n)*(qtp-mhat)/((mhat-2*qtp*k/n)*1/(1+Fbarhat/(k/n))+2*qtp*k/n-qtp)^2
    
    nablah2=qtp*(1-2*k/n)*(1-1/(1+Fbarhat/(k/n)))*1/(1+Fbarhat/(k/n))*mhat/(2*qtp*k/n*1/(1+Fbarhat/(k/n))+qtp-2*qtp*k/n-1/(1+Fbarhat/(k/n))*mhat)^2
    
    S11prime=nablah1^2*S11+nablah2^2*S22+2*nablah1*nablah2*S12
    
    S12prime=nablah1*S12+nablah2*S22
    
    S22prime=S22
    
    h=gammahat
    
    nabla1=log((2*tau-1)/(1-2*k/n))-log((1-tau)/(k/n))+log(1-mhat/qtp)-log(1-mhat/(qtp*((1-tau)/(k/n))^(-h)))-h*log((1-tau)/(k/n))*mhat/(mhat-qtp*((1-tau)/(k/n))^(-h))
    
    nabla2=1-h*mhat/(qtp*((1-tau)/(k/n))^(-h)-mhat)+h*mhat/(qtp-mhat)
    
    varcorr=nabla1^2*S11prime/log(k/(n*(1-tau)))^2+nabla2^2*S22prime/log(k/(n*(1-tau)))^2+2*nabla1*nabla2*S12prime/log(k/(n*(1-tau)))^2
    
    estimup=estimpoint*exp(-(sqrt(varcorr)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1-ci.level)/2)))
    
    estimdown=estimpoint*exp(-(sqrt(varcorr)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1+ci.level)/2)))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint,Upper_bound=estimup))
    
  }
  if (method == "indirect") {
    gammahat=mopest$EVI[k]
    if(gammahat>1){
      stop("Tail index greater than 1 ! Expectile does probably not exist !")
    }
    qtp = quantile(X, 1 - k/n)*(1/gammahat-1)^(-gammahat)
    r = (1 - mean(X)/qtp) * (n/(n - 2 * k)) * (1 + mopest$beta * 
                                                 gammahat * Fbar(X, qtp)^(-mopest$rho)/(gammahat * (1 - 
                                                                                                      mopest$rho - gammahat)))^(-1)
    rbet = (1 - mean(X)/(qtp * (k/(n * (1 - tau)))^(gammahat))) * 
      (1/(2 * tau - 1)) * (1 + mopest$beta * gammahat * (1/gammahat - 
                                                           1)^(-mopest$rho) * (1 - tau)^(-mopest$rho)/(gammahat * 
                                                                                                         (1 - mopest$rho - gammahat)))^(-1)
    estimpoint=(1/gammahat - 1)^(-gammahat) * quantile(X, 1 - 
                                                         k/n) * (k/(n * (1 - tau)))^gammahat * (1 + ((k/(n * 
                                                                                                           (1 - tau)))^mopest$rho - 1)/mopest$rho * mopest$beta * 
                                                                                                  gammahat * (n/k)^mopest$rho) * (1 + ((1/gammahat - 
                                                                                                                                          1)^(-mopest$rho) * rbet^(-mopest$rho) - 1)/mopest$rho * 
                                                                                                                                    mopest$beta * gammahat * (1 - tau)^(-mopest$rho))/(rbet^gammahat)
    quanthat=quantile(X,1-k/n)
    
    expectint=expect(X,1-k/n)
    
    mhat=mean(X)
    
    V11=1
    
    V12=(1/(1-gammahat)-log(1/gammahat-1)) #ordre 1
    
    V12=V12+(3*gammahat-1)/(2*(1-gammahat)^3*k) #order 2
    
    V12=V12+3*(10*gammahat^3-10*gammahat^2+5*gammahat-1)/(4*(1-gammahat)^5*k^2) #order 3
    
    V22=(1+(1/(1-gammahat)-log(1/gammahat-1))^2) #order 1
    
    V22=V22+(1/(1-gammahat)-log(1/gammahat-1))*(3*gammahat-1)/((1-gammahat)^3*k)+0.5/((1-gammahat)^4*k) #order 2
    
    V22=V22+36*(10*gammahat^3-10*gammahat^2+5*gammahat-1)*(1-(1-gammahat)*log(1/gammahat-1))/(24*(1-gammahat)^6*k^2)+(6*gammahat^2-4*gammahat+1)/((1-gammahat)^6*k^2)+20*(3*gammahat-1)^2/(48*(1-gammahat)^6*k^2) #order 3
    
    nabla1=1-gammahat*mhat/((n*(1-tau)/k)^(-gammahat)*(1/gammahat-1)^(-gammahat)*quanthat-mhat)+(log(2*tau-1)-log(1-mhat/((n*(1-tau)/k)^(-gammahat)*(1/gammahat-1)^(-gammahat)*quanthat)))/log(k/(n*(1-tau)))
    
    nabla2=(1-mhat*gammahat/(quanthat*(1/gammahat-1)^(-gammahat)*(k/(n*(1-tau)))^gammahat-mhat))/log(k/(n*(1-tau)))
    
    varcorr=nabla1^2*V11*gammahat^2+nabla2^2*V22*gammahat^2+2*nabla1*nabla2*V12*gammahat^2
    
    estimup=estimpoint*exp(-(sqrt(varcorr)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1-ci.level)/2)))
    
    estimdown=estimpoint*exp(-(sqrt(varcorr)/sqrt(k)*log((k/n)/(1-tau))*qnorm((1+ci.level)/2)))
    
    return(list(Lower_bound=estimdown,Point_estimate=estimpoint,Upper_bound=estimup))
  }
}

#____________________________________________________________________
# internal function (extrapolated direct XMES)
# \widehat{\textrm{XMES}}^{\star}_{\tau'_n}
#____________________________________________________________________
XMES_hat_star_direct <- function(xtab,ytab, k, taunp){
  pn = 1-taunp
  #sample size:
  n=length(ytab)  
  
  #$\widetilde{\xi}_{Y,\tau_n}$ with $\tau_n = 1-k/n$: 
  xi_Y = expectreg::expectile(ytab,probs=1-(k/n)) #use the "expectreg" package
  
  #$\widetilde{\textrm{XMES}}(\tau_n)$ with $\tau_n = 1-k/n$:
  num = sum(xtab*(ytab > xi_Y))      
  den = sum(ytab > xi_Y)       
  XMES = num/den
  
  #$\widehat{\gamma}_X$:
  #gamX = Hill_br(xtab,k)
      ## gamX = min(gamX,1/2)
  gamX = Hill(xtab,k)
  
  #$\widehat{\textrm{XMES}}^*(\tau'_n)$ with $\tau'_n = 1-pn$:
  res = (n*pn/k)^(-gamX) * XMES      
  return(res)
}

#____________________________________________________________________
# internal function (extrapolated direct QMES)
# \widehat{\textrm{MES}}^{\star}_{\tau'_n}
#____________________________________________________________________
QMES_hat_star_direct <- function(xtab,ytab, k, taunp){
  pn = 1-taunp
  #sample size:
  n=length(ytab)        
  
  #intermediate quantile $\widehat{q}_{Y,\tau_n}:=Y_{n-\lfloor n(1-\tau_n) \rfloor,n}$: 
  ysort = sort(ytab)
  q_Y = ysort[n-k] 
  
  #$\widehat{\textrm{QMES}}(\tau_n)$ with $\tau_n = 1-k/n$:
  num = sum(xtab*(ytab > q_Y))      
  den = k       
  QMES = num/den
  
  #$\widehat{\gamma}_X$:
  #gamX = Hill_br(xtab,k)
       ##gamX = min(gamX,1/2)
   gamX = Hill(xtab,k)
  
  #$\widehat{\textrm{QMES}}^*(\tau'_n)$ with $\tau'_n = 1-pn$:
  res = ((n*pn)/k)^(-gamX) * QMES       
  return(res)
}

#____________________________________________________________________
# internal function (extrapolated indirect XMES)
# \widetilde{\textrm{XMES}}^{\star}_{\tau'_n}
#____________________________________________________________________
XMES_tilde_star_indirect <- function(xtab,ytab, k, taunp){
  pn = 1-taunp
  #gamX = Hill_br(xtab,k)
      ##gamX = min(gamX,1/2)
   gamX = Hill(xtab,k)
  
  #gamY = Hill_br(ytab,k) 
      ##gamY = min(gamY,1/2)
   gamY = Hill(ytab,k) 
   
  res = ((1/gamY) - 1)^(-gamX) * QMES_hat_star_direct(xtab,ytab, k, taunp)
  return(res)
}
  
  #_____________________________________________________________________________
  #_____________________________________________________________________________
  #
  #        FIGURE 1.1 (A)-(B)-(C)
  #
  #        Application to the dataset "china_storm" (n=166) 
  #        for the book chapter
  #
  #_____________________________________________________________________________
  #_____________________________________________________________________________
  
  # LOAD DATA ------------------------------------------------------------------
  china_storm <- read.csv2("/Users/.../china_storm.csv")
  # In 1000 US$:
  china_storm_data <- china_storm$Total.Damage..Adjusted...000.US..
  # Total Damages Adjusted Cost in billion USD:
  china_storm_data_B <- china_storm_data/10^6
  #
  data <- china_storm_data_B
  (n <- length(data))
  
  # (A) SCATTERPLOT AND HISTOGRAM ----------------------------------------------
#pdf("/Users/.../Figures/china_storm_histogram.pdf", width=6, height=6)
  par(mfrow=c(1,1))
  #par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
  par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
  hist(data, nclass=30, ylab="", xlab="Total Damages Adjusted Cost in billion USD", main=expression("(A) Histogram and rug plot"), las=1, cex.lab=1.6, cex.axis=1.6,
       cex.main=1.6, bty="l")
  #rug(data, col="red")
  rug(data, ticksize = 0.03, side = 1, lwd = 1, col = "magenta")
#dev.off()  
  
  
  # (B) TESTING FOR TAIL-HEAVINESS ---------------------------------------------
  Tail_Heaviness <- Tail_Heaviness_Test(data, kmax=(length(data)-1))
  pval <- Tail_Heaviness$pval
  kk <- Tail_Heaviness$kk
#pdf("/Users/.../Figures/china_storm_test.pdf", width=6, height=6)
  par(mfrow=c(1,1))
  par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
  plot(y=pval,x=(kk/n)*100,type="l",ylim=c(0,1),col='royalblue',lwd=3, main = expression("(B) Tail heaviness test"), las=1, cex.lab=1.6, cex.axis=1.6,
       cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="" ,xlim=c(0,25)) #,xlim=c(0,20)) # ylab="p-value")
  abline(h=.1, col="chocolate", lty=2, lwd=3)
  abline(h=.05, col="chocolate", lty=3, lwd=4)
  abline(h=.01, col="chocolate", lty=4, lwd=3)
  legend("topright", inset=.04, col=c("royalblue","chocolate","chocolate","chocolate"), lwd=c(3,3,4,3),
         lty=c(1,2,3,4), cex=1.3, bty="n",
         c(eval(bquote(expression("p-value"))),
           eval(bquote("0.10")),
           eval(bquote("0.05")),
           eval(bquote("0.01"))))
#dev.off()  
  

  # (C) BIAS-REDUCED HILL ESTIMATES --------------------------------------------
  k=1:(length(data)-1)  
  hill.br<-mop(data, k, p=0, "RBMOP")$EVI
#pdf("/Users/.../Figures/china_storm_br_hill.pdf", width=6, height=6)
  par(mfrow=c(1,1))
  par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
  plot((k/n)*100, hill.br, type = 'l', col='darkgreen', lwd=3, main = expression("(C) Tail index estimates"), las=1, cex.lab=1.6, cex.axis=1.6,
       cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", ylim=c(0,1.5), xlim=c(0,50)) #, xlim=c(0,40)) 
  #abline(v=35, lty=3, col='gray', lwd=3) 
  abline(h=0.71, lty=2, col='darkgreen', lwd=3) 
  legend("topright", inset=.04, col=c("darkgreen",#"gray",
                                      "darkgreen"), lwd=c(3,3),
         lty=c(1,2), cex=1.3, bty="n",
         c(eval(bquote(expression("BR-Hill"))),
           #eval(bquote("k=35")),
           eval(bquote("0.71"))))
#dev.off() 
  

  #_____________________________________________________________________________
  #_____________________________________________________________________________
  #
  #        FIGURE 1.2 (A)
  #
  #_____________________________________________________________________________
  #_____________________________________________________________________________
   # PLOTS OF THE FOUR SAMPLE RISK MEASURES --------------------------------
   #grid of asymmetry levels:
   tau <- seq(0.9, .999999, length = 500)
   #empirical estimates:
   quant  <- quantile(data, probs = tau, type = 1)
   #extrem <- empirical_extremile(data, tau)
   extrem <- als_extremile(data, tau)
   expect <- expectreg::expectile(data, probs = tau)
   es <- expected_shortfall(data, tau)
   xes <- XES_hat_direct(data, tau)
   
# pdf("/Users/.../Figures/china_storm_comparison_risks.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.35,0))
   #equantile:
   plot(y=quant, x=tau,type="l", col='orange', lwd=4, main = expression("(A) China Storm Losses"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab=expression(tau), ylab="Total Damages Adjusted Cost in billion USD", ylim=c(min(data),max(data))) #, xlim=c(0.7,1))
   #expectile:
   lines(tau, expect, lwd=3, lty=1, col="darkgreen")
   #extremile:
   lines(tau, extrem, lwd=3, lty=1, col="red")
   #ES
   lines(tau, es, lwd=3, lty=1, col="dodgerblue")
   #XES
   lines(tau, xes, lwd=3, lty=1, col="cyan")
   #sample max:
   abline(h = max(data), lwd=.5, lty=3, col = "magenta")
   #data:
   rug(data, ticksize = 0.03, side = 2, lwd = 1, col = "magenta")
   
   legend("bottomright", inset=.02, col=c('orange','darkgreen','red','dodgerblue','cyan'), 
          lty=c(1,1,1,1,1), lwd=c(4,3,3,3,3), cex=1.3, bty="n",
          c(eval(bquote(expression("Quantile"))),
            eval(bquote(expression("Expectile"))),            
            eval(bquote(expression("Extremile"))),
            eval(bquote(expression("ES"))),
            eval(bquote(expression("XES")))))
# dev.off()  
   
  
    
     #_____________________________________________________________________________
     #_____________________________________________________________________________
     #
     #        FIGURE 1.1 (D)-(E)-(F)
     #
     #        Application to the dataset "us_torn" (n=243 and br-hill=0.57) 
     #        for the book chapter
     #
     #_____________________________________________________________________________
     #_____________________________________________________________________________
     
   # LOAD DATA ------------------------------------------------------------------
   us_torn <- read.csv("/Users/.../us_torn.csv")
   # Original loss data (column N) is in Million USD until 2016 where it becomes in USD:
   us_torn_data <- us_torn$loss
   # Data in USD:
   us_torn_data[1:61217] <- us_torn_data[1:61217] * 10^6
   # #-------------------------------------------------------
   # Restrict to the period since 2000:
   us_torn_data_2000 <- us_torn_data[41143:70037]
   # Losses in billion USD:
   us_torn_data_B <- us_torn_data_2000/10^9
   # -------------------------------------------------------
   # losses in excess of $15 Million (n=243 and br-hill=0.57): 
   data <- us_torn_data_B[which(us_torn_data_B > (15/10^3) )]  

   (n <- length(data))
   
   
   # (D) SCATTERPLOT AND HISTOGRAM ----------------------------------------------
#pdf("/Users/.../Figures/us_torn_histogram.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   hist(data, nclass=30, ylab="", xlab="Tornado monetary losses in billion USD", main=expression("(D) Histogram and rug plot"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l")
   #rug(data, col="red")
   rug(data, ticksize = 0.03, side = 1, lwd = 1, col = "magenta")
#dev.off()  
   
   
   # (E) TESTING FOR TAIL-HEAVINESS ---------------------------------------------
   Tail_Heaviness <- Tail_Heaviness_Test(data, kmax=(length(data)-1))
   pval <- Tail_Heaviness$pval
   kk <- Tail_Heaviness$kk
#pdf("/Users/.../Figures/us_torn_test.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   plot(y=pval,x=(kk/n)*100,type="l",ylim=c(0,1),col='royalblue',lwd=3, main = expression("(E) Tail heaviness test"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", xlim=c(0,25)) #, xlim=c(0,20)) # ylab="p-value")
   abline(h=.1, col="chocolate", lty=2, lwd=3)
   abline(h=.05, col="chocolate", lty=3, lwd=4)
   abline(h=.01, col="chocolate", lty=4, lwd=3)
   legend("top", inset=.0, col=c("royalblue","chocolate","chocolate","chocolate"), lwd=c(3,3,4,3),
          lty=c(1,2,3,4), cex=1.3, bty="n",
          c(eval(bquote(expression("p-value"))),
            eval(bquote("0.10")),
            eval(bquote("0.05")),
            eval(bquote("0.01"))))
#dev.off()  
   
   
   # (F) BIAS-REDUCED HILL ESTIMATES --------------------------------------------
   k=1:(length(data)-1)  
   hill.br<-mop(data, k, p=0, "RBMOP")$EVI
#pdf("/Users/.../Figures/us_torn_br_hill.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   plot((k/n)*100, hill.br, type = 'l', col='darkgreen', lwd=3, main = expression("(F) Tail index estimates"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", ylim=c(0,1.5) , xlim=c(0,50)) # , xlim=c(0,40)) 
   #abline(v=35, lty=3, col='gray', lwd=3) 
   abline(h=0.57, lty=2, col='darkgreen', lwd=3) 
  # abline(h=0.59, lty=2, col='cyan', lwd=3) 
   legend("topright", inset=.04, col=c("darkgreen",#"gray",
                                       "darkgreen"), lwd=c(3,3),
          lty=c(1,2), cex=1.3, bty="n",
          c(eval(bquote(expression("BR-Hill"))),
            #eval(bquote("k=35")),
            eval(bquote("0.57"))))
#dev.off() 
   
   #_____________________________________________________________________________
   #_____________________________________________________________________________
   #
   #        FIGURE 1.2 (B)
   #
   #_____________________________________________________________________________
   #____________________________________________________________________________
   # PLOTS OF THE FOUR SAMPLE RISK MEASURES --------------------------------
   #grid of asymmetry levels:
   tau <- seq(0.9, .999999, length = 500)
   #empirical estimates:
   quant  <- quantile(data, probs = tau, type = 1)
   #extrem <- empirical_extremile(data, tau)
   extrem <- als_extremile(data, tau)
   expect <- expectreg::expectile(data, probs = tau)
   es <- expected_shortfall(data, tau)
   xes <- XES_hat_direct(data, tau)
   
 # pdf("/Users/.../Figures/us_torn_comparison_risks.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   #par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.35,0))
   #equantile:
   plot(y=quant, x=tau,type="l", col='orange', lwd=4, main = expression("(B) US Tornado Losses"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab=expression(tau), ylab="Total monetary losses in billion USD", ylim=c(min(data),max(data))) #, xlim=c(0.7,1))
   #expectile:
   lines(tau, expect, lwd=3, lty=1, col="darkgreen")
   #extremile:
   lines(tau, extrem, lwd=3, lty=1, col="red")
   #ES
   lines(tau, es, lwd=3, lty=1, col="dodgerblue")
   #XES
   lines(tau, xes, lwd=3, lty=1, col="cyan")
   #sample max:
   abline(h = max(data), lwd=.5, lty=3, col = "magenta")
   #data:
   rug(data, ticksize = 0.03, side = 2, lwd = 1, col = "magenta")
   
   legend("topleft", inset=.04, col=c('orange','darkgreen','red','dodgerblue','cyan'), 
          lty=c(1,1,1,1,1), lwd=c(4,3,3,3,3), cex=1.3, bty="n",
          c(eval(bquote(expression("Quantile"))),
            eval(bquote(expression("Expectile"))),            
            eval(bquote(expression("Extremile"))),
            eval(bquote(expression("ES"))),
            eval(bquote(expression("XES")))))
# dev.off()    
   
   
   
   
   #_____________________________________________________________________________
   #_____________________________________________________________________________
   #
   #        FIGURE 1.1 (G)-(H)-(I)
   #
   #        Application to the weekly financial returns data 
   #        - X = AIG: American International Group (n=522 and br-hill=0.56) 
   #        - Y = value-weighted market index aggregating three markets: the New 
   #              York Stock Exchange, American Express stock exchange and the 
   #              National Association of Securities Dealers Automated Quotation 
   #              system (n=522 and br-hill=0.39) 
   #        for the book chapter
   #
   #_____________________________________________________________________________
   #_____________________________________________________________________________
   
   #----------------------------------------------------------------------------
   #
   # LOAD THE DATA:
   load("/Users/.../RDatasets//AIG_weekly_returns.RData")
   
   # (G) SCATTERPLOT AND HISTOGRAM ----------------------------------------------
#pdf("/Users/.../Figures/returns_histogram.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   hist(xtab4, nclass=30, ylab="", xlab="Weekly loss returns", main=expression("(G) Histogram and rug plot"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l")
   rug(xtab4, ticksize = 0.03, side = 1, lwd = 1, col = "magenta")
#dev.off()  
   
   # # (H) TESTING FOR TAIL-HEAVINESS ---------------------------------------------
   data <- xtab4
   Tail_Heaviness <- Tail_Heaviness_Test(xtab4, kmax=(length(xtab4)-1))
   pval <- Tail_Heaviness$pval
   kk <- Tail_Heaviness$kk
   n <- length(xtab4)
# pdf("/Users/.../Figures/returns_test.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   plot(y=pval,x=(kk/n)*100,type="l",ylim=c(0,1),col='royalblue',lwd=3, main = expression("(H) Tail heaviness test"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", xlim=c(0,25)) # ylab="p-value")
   abline(h=.1, col="chocolate", lty=2, lwd=3)
   abline(h=.05, col="chocolate", lty=3, lwd=4)
   abline(h=.01, col="chocolate", lty=4, lwd=3)
   legend("topright", inset=.0, col=c("royalblue","chocolate","chocolate","chocolate"), lwd=c(3,3,4,3),
          lty=c(1,2,3,4), cex=1.3, bty="n",
          c(eval(bquote(expression("p-value"))),
            eval(bquote("0.10")),
            eval(bquote("0.05")),
            eval(bquote("0.01"))))
# dev.off()  
   
   
   # (I) BIAS-REDUCED HILL ESTIMATES --------------------------------------------
   k=1:(length(xtab4)-1)  
   hill.br<- mop(xtab4, k, p=0, "RBMOP")$EVI
#pdf("/Users/.../Figures/returns_br_hill.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
   plot((k/n)*100, hill.br, type = 'l', col='darkgreen', lwd=3, main = expression("(I) Tail index estimates"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", ylim=c(0,1.5) , xlim=c(0,50)) # , xlim=c(0,40)) 
   abline(h=0.56, lty=2, col='darkgreen', lwd=3) 
   legend("topleft", inset=.04, col=c("darkgreen",#"gray",
                                       "darkgreen"), lwd=c(3,3),
          lty=c(1,2), cex=1.3, bty="n",
          c(eval(bquote(expression("BR-Hill"))),
             eval(bquote("0.56"))))
#dev.off() 
   
 
   #_____________________________________________________________________________
   #_____________________________________________________________________________
   #
   #        FIGURE 1.2 (C)
   #
   #_____________________________________________________________________________
   #____________________________________________________________________________
   # PLOTS OF THE FIVE SAMPLE RISK MEASURES --------------------------------
   #grid of asymmetry levels:
   tau <- seq(0.9, .999999, length = 500)
   #empirical estimates:
   quant  <- quantile(xtab4, probs = tau, type = 1)
   extrem <- als_extremile(xtab4, tau)
   expect <- expectreg::expectile(xtab4, probs = tau)
   es <- expected_shortfall(xtab4, tau)
   xes <- XES_hat_direct(xtab4, tau)
   
# pdf("/Users/.../Figures/returns_comparison_risks.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.35,0))
   #equantile:
   plot(y=quant, x=tau,type="l", col='orange', lwd=4, main = expression("(C) AIG financial returns"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab=expression(tau), ylab="Loss  Returns", ylim=c(0,max(xtab4))) 
   #expectile:
   lines(tau, expect, lwd=3, lty=1, col="darkgreen")
   #extremile:
   lines(tau, extrem, lwd=3, lty=1, col="red")
   #ES
   lines(tau, es, lwd=3, lty=1, col="dodgerblue")
   #XES
   lines(tau, xes, lwd=3, lty=1, col="cyan")
   #sample max:
   abline(h = max(xtab4), lwd=.5, lty=3, col = "magenta")
   #data:
   #rug(xtab4, ticksize = 0.03, side = 2, lwd = 1, col = "magenta")
   rug(xtab4[which(xtab4 > 0 )], ticksize = 0.03, side = 2, lwd = 1, col = "magenta")
   
   legend("topleft", inset=.04, col=c('orange','darkgreen','red','dodgerblue','cyan'), 
          lty=c(1,1,1,1,1), lwd=c(4,3,3,3,3), cex=1.3, bty="n",
          c(eval(bquote(expression("Quantile"))),
            eval(bquote(expression("Expectile"))),            
            eval(bquote(expression("Extremile"))),
            eval(bquote(expression("ES"))),
            eval(bquote(expression("XES")))))
# dev.off()    
   
   
   #_____________________________________________________________________________
   #_____________________________________________________________________________
   #
   #        FIGURE 1.2 (D)
   #
   #_____________________________________________________________________________
   #____________________________________________________________________________
   # PLOTS OF THE FIVE SAMPLE RISK MEASURES --------------------------------
   data <- ytab
   #grid of asymmetry levels:
   tau <- seq(0.9, .999999, length = 500)
   #empirical estimates:
   quant  <- quantile(ytab, probs = tau, type = 1)
   #extrem <- empirical_extremile(ytab, tau)
   extrem <- als_extremile(ytab, tau)
   expect <- expectreg::expectile(ytab, probs = tau)
   es <- expected_shortfall(ytab, tau)
   xes <- XES_hat_direct(ytab, tau)
   
  # pdf("/Users/.../Figures/MIreturns_comparison_risks.pdf", width=6, height=6)
   par(mfrow=c(1,1))
   par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.35,0))
   #equantile:
   plot(y=quant, x=tau,type="l", col='orange', lwd=4, main = expression("(D) Market index returns"), las=1, cex.lab=1.6, cex.axis=1.6,
        cex.main=1.6, bty="l", xlab=expression(tau), ylab="    Loss    Returns", ylim=c(0,max(ytab))) 
   #expectile:
   lines(tau, expect, lwd=3, lty=1, col="darkgreen")
   #extremile:
   lines(tau, extrem, lwd=3, lty=1, col="red")
   #ES
   lines(tau, es, lwd=3, lty=1, col="dodgerblue")
   #XES
   lines(tau, xes, lwd=3, lty=1, col="cyan")
   #sample max:
   abline(h = max(ytab), lwd=.5, lty=3, col = "magenta")
   #data:
   rug(ytab[which(ytab > 0 )], ticksize = 0.03, side = 2, lwd = 1, col = "magenta")
   
   legend("topleft", inset=.04, col=c('orange','darkgreen','red','dodgerblue','cyan'), 
          lty=c(1,1,1,1,1), lwd=c(4,3,3,3,3), cex=1.3, bty="n",
          c(eval(bquote(expression("Quantile"))),
            eval(bquote(expression("Expectile"))),            
            eval(bquote(expression("Extremile"))),
            eval(bquote(expression("ES"))),
            eval(bquote(expression("XES")))))
  
#   dev.off()    
   
   #----------------------------------------------------------------------------
   #----------------------------------------------------------------------------
   #       FIGURE 1.3
   #
   #       EXTRAPOLATED QES ESTIMATES
   #
   #----------------------------------------------------------------------------
   #----------------------------------------------------------------------------
   
   #_______________________________
   #
   #    "china_storm" (n=166) 
   #       
   #_______________________________  
   
   # LOAD DATA ------------------------------------------------------------------
   china_storm <- read.csv2("/Users/.../china_storm.csv")
   # In 1000 US$:
   china_storm_data <- china_storm$Total.Damage..Adjusted...000.US..
   # Total Damages Adjusted Cost in billion USD:
   china_storm_data_B <- china_storm_data/10^6
   #
   data <- china_storm_data_B
   n <- length(data)

   #------------- 
   ytab <- data
   (Yn = max(ytab))
   ysort=sort(ytab)   
   
   ##grid of values of "k":
   kl = 1 
   ku = 42 # .25*166
   kk = kl:ku 
   nk = length(kk)
   
   ##estreme level:
   taunp <- 1-1/n
   
   ##Initialization of ES estimates:
   line_max = cbind(rep(0, nk))    #Sample maximum
   gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
   qes_hat = cbind(rep(0, nk))     #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   qes_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
   # CIs:
   LB_tilde <- cbind(rep(0, nk))
   UB_tilde <- cbind(rep(0, nk))
   LB_hat <- cbind(rep(0, nk))
   UB_hat <- cbind(rep(0, nk))
   LB_q <-  cbind(rep(0, nk)) 
   UB_q <-  cbind(rep(0, nk))   
     
   ##Calculation of ES estimates:
   for (i in 1:nk)
   { 
     #Sample fraction:        	
     k <- kk[i]
     
     #Sample maximum:
     line_max[i] <- Yn
     
     #BR-Hill gammma estimate:        	         	     
     gamm  <- Hill_br(ytab, k)
     gam[i] <- gamm
     
     # QES direct $\widehat{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_hat[i] <- QES_hat_star_direct(ytab, k, taunp)
     #CI_hat:
     z <- 1.959964 

     # QES indirect $\widetilde{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_tilde[i] <- QES_tilde_star_indirect(ytab, k, taunp)
     #CI_tilde:
     LB_tilde[i] <- qes_tilde[i] - z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k)
     UB_tilde[i] <- qes_tilde[i] + z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k) 
     
     # Weissman quantile estimator:
     q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
     # CI:
    LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
    UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
   }
   
#   save(kk, n, line_max,  gam, qes_hat, qes_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//china_storm_ES.RData")

     #_______________________________
     #
     #    "us_torn"  
     #       
     #_______________________________  
     
     # LOAD DATA ------------------------------------------------------------------
   us_torn <- read.csv("/Users/.../us_torn.csv")
   # Original loss data (column N) is in Million USD until 2016 where it becomes in USD:
   us_torn_data <- us_torn$loss
   # Data in USD:
   us_torn_data[1:61217] <- us_torn_data[1:61217] * 10^6
   # Restrict to the period since 2000:
   us_torn_data_2000 <- us_torn_data[41143:70037]
   # Losses in billion USD:
   us_torn_data_B <- us_torn_data_2000/10^9
   # losses in excess of $15 Million (n=243 and br-hill=0.57): ---------------------------- 
   data <- us_torn_data_B[which(us_torn_data_B > (15/10^3) )]  # NICE for the Antoine paper 
   n <- length(data)
   
   
   #------------- 
   ytab <- data
   Yn = max(ytab)
   ysort=sort(ytab)   
   
   ##grid of values of "k":
   kl = 1 
   ku = 61 # .25*243
   kk = kl:ku 
   nk = length(kk)
   
   ##estreme level:
   taunp <- 1-1/n
   
   ##Initialization of ES estimates:
   line_max = cbind(rep(0, nk))    #Sample maximum
   gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
   qes_hat = cbind(rep(0, nk))     #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   qes_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
   # CIs:
   LB_tilde <- cbind(rep(0, nk))
   UB_tilde <- cbind(rep(0, nk))
   LB_hat <- cbind(rep(0, nk))
   UB_hat <- cbind(rep(0, nk))
   LB_q <-  cbind(rep(0, nk)) 
   UB_q <-  cbind(rep(0, nk))   
   
   ##Calculation of ES estimates:
   for (i in 1:nk)
   { 
     #Sample fraction:        	
     k <- kk[i]
     
     #Sample maximum:
     line_max[i] <- Yn
     
     #BR-Hill gammma estimate:        	         	     
     gamm  <- Hill_br(ytab, k)
     gam[i] <- gamm
     
     # QES direct $\widehat{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_hat[i] <- QES_hat_star_direct(ytab, k, taunp)
     #CI_hat:
     z <- 1.959964 

     # QES indirect $\widetilde{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_tilde[i] <- QES_tilde_star_indirect(ytab, k, taunp)
     #CI_tilde:
     LB_tilde[i] <- qes_tilde[i] - z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k)
     UB_tilde[i] <- qes_tilde[i] + z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k) 
     
     # Weissman quantile estimator:
     q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
     # CI:
     LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
     UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
   }
   
#   save(kk, n, line_max,  gam, qes_hat, qes_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//us_torn_ES.RData")

     #_______________________________
     #
     #   "AIG's weekly loss returns"  
     #       
     #_______________________________ 
     
   # LOAD THE DATA:
   load("/Users/.../RDatasets//AIG_weekly_returns.RData")

   #------------- 
   xtab <- xtab4
   n <- length(xtab)
   Yn = max(xtab)
   ysort=sort(xtab)   
   
   ##grid of values of "k":
   kl = 1 
   ku = 131 # .25*522
   kk = kl:ku 
   nk = length(kk)
   
   ##estreme level:
   taunp <- 1-1/n
   
   ##Initialization of ES estimates:
   line_max = cbind(rep(0, nk))    #Sample maximum
   gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
   qes_hat = cbind(rep(0, nk))     #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   qes_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
   # CIs:
   LB_tilde <- cbind(rep(0, nk))
   UB_tilde <- cbind(rep(0, nk))
   LB_hat <- cbind(rep(0, nk))
   UB_hat <- cbind(rep(0, nk))
   LB_q <-  cbind(rep(0, nk)) 
   UB_q <-  cbind(rep(0, nk))   
   
   ##Calculation of ES estimates:
   for (i in 1:nk)
   { 
     #Sample fraction:        	
     k <- kk[i]
     
     #Sample maximum:
     line_max[i] <- Yn
     
     #BR-Hill gammma estimate:        	         	     
     gamm  <- Hill_br(xtab, k)
     gam[i] <- gamm
     
     # QES direct $\widehat{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_hat[i] <- QES_hat_star_direct(xtab, k, taunp)
     #CI_hat:
     z <- 1.959964 

     # QES indirect $\widetilde{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_tilde[i] <- QES_tilde_star_indirect(xtab, k, taunp)
     #CI_tilde:
     LB_tilde[i] <- qes_tilde[i] - z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k)
     UB_tilde[i] <- qes_tilde[i] + z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k) 
     
     # Weissman quantile estimator:
     q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
     # CI:
     LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
     UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
   }
   
 #  save(kk, n, line_max,  gam, qes_hat, qes_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//AIG_ES.RData")
   
     #_______________________________
     #
     # Market index weekly loss returns"  
     #       
     #_______________________________ 
     
   # LOAD THE DATA:
   load("/Users/.../RDatasets//AIG_weekly_returns.RData")

   #------------- 
   n <- length(ytab)
   Yn = max(ytab)
   ysort=sort(ytab)   
   
   ##grid of values of "k":
   kl = 1 
   ku = 131 # .25*522
   kk = kl:ku 
   nk = length(kk)
   
   ##estreme level:
   taunp <- 1-1/n
   
   ##Initialization of ES estimates:
   line_max = cbind(rep(0, nk))    #Sample maximum
   gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
   qes_hat = cbind(rep(0, nk))     #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   qes_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{QES}}^{\star}_{p_n}(alpha)$
   q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
   # CIs:
   LB_tilde <- cbind(rep(0, nk))
   UB_tilde <- cbind(rep(0, nk))
   LB_hat <- cbind(rep(0, nk))
   UB_hat <- cbind(rep(0, nk))
   LB_q <-  cbind(rep(0, nk)) 
   UB_q <-  cbind(rep(0, nk))   
   
   ##Calculation of ES estimates:
   for (i in 1:nk)
   { 
     #Sample fraction:        	
     k <- kk[i]
     
     #Sample maximum:
     line_max[i] <- Yn
     
     #BR-Hill gammma estimate:        	         	     
     gamm  <- Hill_br(ytab, k)
     gam[i] <- gamm
     
     # QES direct $\widehat{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_hat[i] <- QES_hat_star_direct(ytab, k, taunp)
     #CI_hat:
     z <- 1.959964 
     LB_hat[i] <- qes_hat[i] - z * log(k/(n*(1/n))) * qes_hat[i] * gamm/sqrt(k)
     UB_hat[i] <- qes_hat[i] + z * log(k/(n*(1/n))) * qes_hat[i] * gamm/sqrt(k) 
     
     # QES indirect $\widetilde{\textrm{QES}}^{\star}_{p_n=1-1/n}$:            
     qes_tilde[i] <- QES_tilde_star_indirect(ytab, k, taunp)
     #CI_tilde:
     LB_tilde[i] <- qes_tilde[i] - z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k)
     UB_tilde[i] <- qes_tilde[i] + z * log(k/(n*(1/n))) * qes_tilde[i] * gamm/sqrt(k) 
     
     # Weissman quantile estimator:
     q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
     # CI:
     LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
     UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
   }
   
 #  save(kk, n, line_max,  gam, qes_hat, qes_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//Index_ES.RData")
   
   #____________________________________________________________________
   #
   # Figure "extrap_ES_AC.pdf":
   #     
   #____________________________________________________________________   
   
   
# pdf("/Users/.../Figures/extrap_ES_AC.pdf", width=6, height=9) #height=6)
   
   #require(grid)
   grid.newpage()
   pushViewport(viewport(layout = grid.layout(2,2)))
   
   define_region = function(row, col){
     viewport(layout.pos.row=row, layout.pos.col=col)
   }
   
   # (A) China Storm Losses
   load("/Users/.../RDatasets//china_storm_ES.RData")
   
   dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
   dff <-data.frame(xxc = (kk/n)*100, yyc = qes_tilde, gam)    # rainbow                                   
   df5 <-data.frame(xxc = (kk/n)*100, yyc = qes_hat, gam)      # solid red 
   df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
   
   df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
   df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
   
   df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
   df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
   
   dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
   print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
           scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
           scale_y_continuous(name = "ES")+
        #   scale_x_continuous("Effective sample fraction x 100%")+ 
           scale_x_continuous("")+ 
           #
           geom_line(size = .7,data = df5, colour = "red", linetype=1)+
           # 
           geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
           # 
           geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
           geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
           #
           # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
           # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
           labs(title = "(A) China Storm Losses")+ 
           theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                              panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
         vp=define_region(1,1:2)) 
   
   # (C) AIG Loss Returns
   load("/Users/.../RDatasets//AIG_ES.RData")
   
   dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
   dff <-data.frame(xxc = (kk/n)*100, yyc = qes_tilde, gam)    # rainbow                                   
   df5 <-data.frame(xxc = (kk/n)*100, yyc = qes_hat, gam)      # solid red 
   df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
   
   df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
   df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
   
   df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
   df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
   
   dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
   print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
           scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
           scale_y_continuous(name = "ES")+
           scale_x_continuous("Effective sample fraction x 100%")+ 
           #
           geom_line(size = .7,data = df5, colour = "red", linetype=1)+
           # 
           geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
           # 
           geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
           geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
           #
           # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
           # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
           labs(title = "(C) AIG Loss Returns")+ 
           theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                              panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
         vp=define_region(2,1:2))   
  
# dev.off()      
   

   #__________________________________
   #
   # Figure "extrap_ES_BD.pdf":
   #     
   #__________________________________   
   
   
# pdf("/Users/.../Figures/extrap_ES_BD.pdf", width=6, height=9) #height=6)
   
   #require(grid)
   grid.newpage()
   pushViewport(viewport(layout = grid.layout(2,2)))
   
   define_region = function(row, col){
     viewport(layout.pos.row=row, layout.pos.col=col)
   }
   
   
   # (B) US Tornado Losses
   load("/Users/.../RDatasets//us_torn_ES.RData")
   
   dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
   dff <-data.frame(xxc = (kk/n)*100, yyc = qes_tilde, gam)    # rainbow                                   
   df5 <-data.frame(xxc = (kk/n)*100, yyc = qes_hat, gam)      # solid red 
   df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
   
   df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
   df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
   
   df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
   df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
   
   dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
   print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
           scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
           scale_y_continuous(name = "ES")+
        #   scale_x_continuous("Effective sample fraction x 100%")+ 
           scale_x_continuous("")+ 
           #
           geom_line(size = .7,data = df5, colour = "red", linetype=1)+
           # 
           geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
           # 
           geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
           geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
           #
           # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
           # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
           labs(title = "(B) US Tornado Losses")+ 
           theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                              panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
         vp=define_region(1,1:2))

   # (D) Market Index Loss Returns
   load("/Users/.../RDatasets//Index_ES.RData")
   
   dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
   dff <-data.frame(xxc = (kk/n)*100, yyc = qes_tilde, gam)    # rainbow                                   
   df5 <-data.frame(xxc = (kk/n)*100, yyc = qes_hat, gam)      # solid red 
   df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
   
   df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
   df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
   
   df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
   df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
   
   df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
   df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
   
   dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
   print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
           scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
           scale_y_continuous(name = "ES")+
           scale_x_continuous("Effective sample fraction x 100%")+ 
           #
           geom_line(size = .7,data = df5, colour = "red", linetype=1)+
           # 
           geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
           # 
           geom_line(size = .6,data = df_LB_hat, colour = "red", linetype=2)+
           geom_line(size = .6,data = df_UB_hat, colour = "red", linetype=2)+  
           geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
           geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
           #
           # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
           # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
           labs(title = "(D) Market Index Loss Returns")+ 
           theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                              panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
         vp=define_region(2,1:2)) 
   
# dev.off()        
   
 
 
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 #
 #       FIGURE 1.6  
 #
 #       EXTRAPOLATED XES ESTIMATES
 #
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 
 #_______________________________
 #
 #    "china_storm" (n=166) 
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 china_storm <- read.csv2("/Users/.../china_storm.csv")
 # In 1000 US$:
 china_storm_data <- china_storm$Total.Damage..Adjusted...000.US..
 # Total Damages Adjusted Cost in billion USD:
 china_storm_data_B <- china_storm_data/10^6
 #
 data <- china_storm_data_B
 n <- length(data)
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 42 # .25*166
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_hat[i] <- XES_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_tilde[i] <- XES_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//china_storm_XES.RData")

 #_______________________________
 #
 #    "us_torn"  
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 us_torn <- read.csv("/Users/.../us_torn.csv")
 # Original loss data (column N) is in Million USD until 2016 where it becomes in USD:
 us_torn_data <- us_torn$loss
 # Data in USD:
 us_torn_data[1:61217] <- us_torn_data[1:61217] * 10^6
 # Restrict to the period since 2000:
 us_torn_data_2000 <- us_torn_data[41143:70037]
 # Losses in billion USD:
 us_torn_data_B <- us_torn_data_2000/10^9
 # losses in excess of $15 Million (n=243 and br-hill=0.57): ---------------------------- 
 data <- us_torn_data_B[which(us_torn_data_B > (15/10^3) )]  # NICE for the Antoine paper 
 n <- length(data)
 
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 61 # .25*243
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_hat[i] <- XES_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_tilde[i] <- XES_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//us_torn_XES.RData")
 
 #_______________________________
 #
 #   "AIG's weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 xtab <- xtab4
 n <- length(xtab)
 Yn = max(xtab)
 ysort=sort(xtab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(xtab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_hat[i] <- XES_hat_star_direct(xtab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_tilde[i] <- XES_tilde_star_indirect(xtab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//AIG_XES.RData")
 
 #_______________________________
 #
 # Market index weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 n <- length(ytab)
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_hat[i] <- XES_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 
   LB_hat[i] <- XES_hat[i] - z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k)
   UB_hat[i] <- XES_hat[i] + z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k) 
   
   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   XES_tilde[i] <- XES_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//Index_XES.RData")
 

 #____________________________________________________________________
 #
 # Figure "extrap_XES_AC.pdf":
 #     
 #____________________________________________________________________   
 
 
 #pdf("/Users/.../Figures/extrap_XES_AC.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (A) China Storm Losses
 load("/Users/.../RDatasets//china_storm_XES.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "XES")+
      #   scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         #
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(A) China Storm Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))
 
 # (C) AIG Loss Returns
 load("/Users/.../RDatasets//AIG_XES.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "XES")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(C) AIG Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))  
   
# dev.off()      
 
 
 #__________________________________
 #
 # Figure "extrap_XES_BD.pdf":
 #     
 #__________________________________   
 
 
# pdf("/Users/.../Figures/extrap_XES_BD.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }

 
 # (B) US Tornado Losses
 load("/Users/.../RDatasets//us_torn_XES.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "XES")+
       #  scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(B) US Tornado Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))
 
 
 # (D) Market Index Loss Returns
 load("/Users/.../RDatasets//Index_XES.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "XES")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .6,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(D) Market Index Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))   
 
# dev.off()        
 
 
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 #
 #       FIGURE 1.4
 #
 #       EXTRAPOLATED EXTREMILE ESTIMATES
 #
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 
 #_______________________________
 #
 #    "china_storm" (n=166) 
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 china_storm <- read.csv2("/Users/.../china_storm.csv")
 # In 1000 US$:
 china_storm_data <- china_storm$Total.Damage..Adjusted...000.US..
 # Total Damages Adjusted Cost in billion USD:
 china_storm_data_B <- china_storm_data/10^6
 #
 data <- china_storm_data_B
 n <- length(data)
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 42 # .25*166
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 x_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 x_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_hat[i] <- xtremile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_tilde[i] <- xtremile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- x_tilde[i] - z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- x_tilde[i] + z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, x_hat, x_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//china_storm_x.RData")

 #_______________________________
 #
 #    "us_torn"  
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 us_torn <- read.csv("/Users/.../us_torn.csv")
 # Original loss data (column N) is in Million USD until 2016 where it becomes in USD:
 us_torn_data <- us_torn$loss
 # Data in USD:
 us_torn_data[1:61217] <- us_torn_data[1:61217] * 10^6
 # Restrict to the period since 2000:
 us_torn_data_2000 <- us_torn_data[41143:70037]
 # Losses in billion USD:
 us_torn_data_B <- us_torn_data_2000/10^9
 # losses in excess of $15 Million (n=243 and br-hill=0.57): ---------------------------- 
 data <- us_torn_data_B[which(us_torn_data_B > (15/10^3) )]  # NICE for the Antoine paper 
 n <- length(data)
 
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 61 # .25*243
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 x_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 x_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_hat[i] <- xtremile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_tilde[i] <- xtremile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- x_tilde[i] - z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- x_tilde[i] + z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, x_hat, x_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//us_torn_x.RData")
 

 #_______________________________
 #
 #   "AIG's weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 xtab <- xtab4
 n <- length(xtab)
 Yn = max(xtab)
 ysort=sort(xtab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 x_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 x_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(xtab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_hat[i] <- xtremile_hat_star_direct(xtab, k, taunp)
   #CI_hat:
   z <- 1.959964 
 
   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   x_tilde[i] <- xtremile_tilde_star_indirect(xtab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- x_tilde[i] - z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- x_tilde[i] + z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, x_hat, x_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//AIG_x.RData")
 

 
 #_______________________________
 #
 # Market index weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 n <- length(ytab)
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 x_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 x_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   x_hat[i] <- xtremile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 
   LB_hat[i] <- x_hat[i] - z * log(k/(n*(1/n))) * x_hat[i] * gamm/sqrt(k)
   UB_hat[i] <- x_hat[i] + z * log(k/(n*(1/n))) * x_hat[i] * gamm/sqrt(k) 
   
   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   x_tilde[i] <- xtremile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- x_tilde[i] - z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- x_tilde[i] + z * log(k/(n*(1/n))) * x_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, x_hat, x_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//Index_x.RData")

 #____________________________________________________________________
 #
 # Figure "extrap_X_AC.pdf":
 #     
 #____________________________________________________________________   
 
 
# pdf("/Users/.../Figures/extrap_X_AC.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (A) China Storm Losses
 load("/Users/.../RDatasets//china_storm_x.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = x_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = x_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Extremile")+
      #   scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         #
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(A) China Storm Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))
 
 # (C) AIG Loss Returns
 load("/Users/.../RDatasets//AIG_x.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = x_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = x_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Extremile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(C) AIG Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))   
 
 # dev.off()      
 
 
 #__________________________________
 #
 # Figure "extrap_X_BD.pdf":
 #     
 #__________________________________   
 
 
# pdf("/Users/.../Figures/extrap_X_BD.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (B) US Tornado Losses
 load("/Users/.../RDatasets//us_torn_x.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = x_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = x_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Extremile")+
     #    scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(B) US Tornado Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))
 
 
 # (D) Market Index Loss Returns
 load("/Users/.../RDatasets//Index_x.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = x_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = x_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Extremile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .6,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(D) Market Index Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))   
 
# dev.off()        
 
   
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 #
 #       FIGURE 1.5
 #
 #       EXTRAPOLATED EXPECTILE ESTIMATES
 #
 #----------------------------------------------------------------------------
 #----------------------------------------------------------------------------
 
 #_______________________________
 #
 #    "china_storm" (n=166) 
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 china_storm <- read.csv2("/Users/.../china_storm.csv")
 # In 1000 US$:
 china_storm_data <- china_storm$Total.Damage..Adjusted...000.US..
 # Total Damages Adjusted Cost in billion USD:
 china_storm_data_B <- china_storm_data/10^6
 #
 data <- china_storm_data_B
 n <- length(data)
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 42 # .25*166
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//china_storm_e.RData")
 
 
 
 #_______________________________
 #
 #    "us_torn"  
 #       
 #_______________________________  
 
 # LOAD DATA ------------------------------------------------------------------
 us_torn <- read.csv("/Users/.../us_torn.csv")
 # Original loss data (column N) is in Million USD until 2016 where it becomes in USD:
 us_torn_data <- us_torn$loss
 # Data in USD:
 us_torn_data[1:61217] <- us_torn_data[1:61217] * 10^6
 # Restrict to the period since 2000:
 us_torn_data_2000 <- us_torn_data[41143:70037]
 # Losses in billion USD:
 us_torn_data_B <- us_torn_data_2000/10^9
 # losses in excess of $15 Million (n=243 and br-hill=0.57): ---------------------------- 
 data <- us_torn_data_B[which(us_torn_data_B > (15/10^3) )]  # NICE for the Antoine paper 
 n <- length(data)
 
 
 #------------- 
 ytab <- data
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 61 # .25*243
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//us_torn_e.RData")
 
 
 
 
 #_______________________________
 #
 #   "AIG's weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 xtab <- xtab4
 n <- length(xtab)
 Yn = max(xtab)
 ysort=sort(xtab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(xtab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(xtab, k, taunp)
   #CI_hat:
   z <- 1.959964 

   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(xtab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q,  file="/Users/.../RDatasets//AIG_e.RData")
 

 #_______________________________
 #
 # Market index weekly loss returns"  
 #       
 #_______________________________ 
 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//AIG_weekly_returns.RData")

 n <- length(ytab)
 Yn = max(ytab)
 ysort=sort(ytab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(ytab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(ytab, k, taunp)
   #CI_hat:
   z <- 1.959964 
   LB_hat[i] <- e_hat[i] - z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k)
   UB_hat[i] <- e_hat[i] + z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k) 
   
   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(ytab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(ytab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//Index_e.RData")
 
 
 #____________________________________________________________________
 #
 # Figure "extrap_E_AC.pdf":
 #     
 #____________________________________________________________________   
 
 
# pdf("/Users/.../Figures/extrap_E_AC.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (A) China Storm Losses
 load("/Users/.../RDatasets//china_storm_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
      #   scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         #
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(A) China Storm Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))
 
 # (C) AIG Loss Returns
 load("/Users/.../RDatasets//AIG_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(C) AIG Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))   
   
# dev.off()      
 
 
 #__________________________________
 #
 # Figure "extrap_E_BD.pdf":
 #     
 #__________________________________   
 
 #pdf("/Users/.../Figures/extrap_E_BD.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (B) US Tornado Losses
 load("/Users/.../RDatasets//us_torn_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
      #   scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(B) US Tornado Losses")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(1,1:2))

 # (D) Market Index Loss Returns
 load("/Users/.../RDatasets//Index_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .7,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .6,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .6,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .6,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .6,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+  
         labs(title = "(D) Market Index Loss Returns")+ 
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
       vp=define_region(2,1:2))   
 
# dev.off()        
 
  
#----------------------------------------------------------------------------
#----------------------------------------------------------------------------
#
#       FIGURE 1.8
#
#       EXTRAPOLATED QMES AND XMES ESTIMATES
#
#----------------------------------------------------------------------------
#----------------------------------------------------------------------------

#_______________________________
#
#  1. AIG 
#       
#_______________________________ 

# LOAD THE DATA:
load("/Users/.../RDatasets//AIG_weekly_returns.RData")

xtab <- xtab4
n <- length(xtab)

##grid of values of "k":
kl = 1 
ku = 131 # .25*522
kk = kl:ku 
nk = length(kk)

##estreme level:
taunp <- 1-1/n

##Initialization of MES estimates:
gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate of X
XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
QES = cbind(rep(0, nk))  # usual Weissman quantile estimator
# CIs:
LB_tilde <- cbind(rep(0, nk))
UB_tilde <- cbind(rep(0, nk))
LB_hat <- cbind(rep(0, nk))
UB_hat <- cbind(rep(0, nk))
LB_q <-  cbind(rep(0, nk)) 
UB_q <-  cbind(rep(0, nk))   

##Calculation of MES estimates:
for (i in 1:nk)
{ 
  #Sample fraction:        	
  k <- kk[i]
  
  ## BR-Hill gammma estimate of X:        	         	     
  #gamm  <- Hill_br(xtab, k)
  ## Hill gammma estimate of X:  
  gamm  <- Hill(xtab, k)
  gam[i] <- gamm
  
  # XMES direct $\widehat{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_hat[i] <- XMES_hat_star_direct(xtab,ytab, k, taunp)
  #CI_hat:
  z <- 1.959964 

  # XMES indirect $\widetilde{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_tilde[i] <- XMES_tilde_star_indirect(xtab,ytab, k, taunp)

  # QMES:
  QES[i] <- QMES_hat_star_direct(xtab,ytab, k, taunp)
}

#save(kk, n,  gam, XES_hat, XES_tilde, QES, file="/Users/.../RDatasets//AIG_MES.RData")


  #_______________________________
  #
  #   2. Citigroup Inc. (C)
  #
  #_______________________________
# LOAD THE DATA:
load("/Users/.../RDatasets//C_weekly_returns.RData")

xtab <- xtab
n <- length(xtab)

##grid of values of "k":
kl = 1
ku = 131 # .25*522
kk = kl:ku
nk = length(kk)

##estreme level:
taunp <- 1-1/n

##Initialization of MES estimates:
gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate of X
XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
QES = cbind(rep(0, nk))  # usual Weissman quantile estimator
# CIs:
LB_tilde <- cbind(rep(0, nk))
UB_tilde <- cbind(rep(0, nk))
LB_hat <- cbind(rep(0, nk))
UB_hat <- cbind(rep(0, nk))
LB_q <-  cbind(rep(0, nk))
UB_q <-  cbind(rep(0, nk))

##Calculation of MES estimates:
for (i in 1:nk)
{
  #Sample fraction:
  k <- kk[i]

  ## BR-Hill gammma estimate of X:
  #gamm  <- Hill_br(xtab, k)
  ## Hill gammma estimate of X:
  gamm  <- Hill(xtab, k)
  gam[i] <- gamm

  # XMES direct $\widehat{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:
  XES_hat[i] <- XMES_hat_star_direct(xtab,ytab, k, taunp)
  #CI_hat:
  z <- 1.959964

  # XMES indirect $\widetilde{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:
  XES_tilde[i] <- XMES_tilde_star_indirect(xtab,ytab, k, taunp)

  # QMES:
  QES[i] <- QMES_hat_star_direct(xtab,ytab, k, taunp)
}

#save(kk, n,  gam, XES_hat, XES_tilde, QES, file="/Users/.../RDatasets//C_MES.RData")



  #_______________________________
  #
  #   3. JPMorgan Chase (JPM)
  #       
  #_______________________________ 
  # LOAD THE DATA:
  load("/Users/.../RDatasets//JPM_weekly_returns.RData")

n <- length(xtab)

##grid of values of "k":
kl = 1 
ku = 131 # .25*522
kk = kl:ku 
nk = length(kk)

##estreme level:
taunp <- 1-1/n

##Initialization of MES estimates:
gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate of X
XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
QES = cbind(rep(0, nk))  # usual Weissman quantile estimator
# CIs:
LB_tilde <- cbind(rep(0, nk))
UB_tilde <- cbind(rep(0, nk))
LB_hat <- cbind(rep(0, nk))
UB_hat <- cbind(rep(0, nk))
LB_q <-  cbind(rep(0, nk)) 
UB_q <-  cbind(rep(0, nk))   

##Calculation of MES estimates:
for (i in 1:nk)
{ 
  #Sample fraction:        	
  k <- kk[i]
  
  ## BR-Hill gammma estimate of X:        	         	     
  #gamm  <- Hill_br(xtab, k)
  ## Hill gammma estimate of X:  
  gamm  <- Hill(xtab, k)
  gam[i] <- gamm
  
  # XMES direct $\widehat{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_hat[i] <- XMES_hat_star_direct(xtab,ytab, k, taunp)
  #CI_hat:
  z <- 1.959964 
  LB_hat[i] <- XES_hat[i] - z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k)
  UB_hat[i] <- XES_hat[i] + z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k)
  
  # XMES indirect $\widetilde{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_tilde[i] <- XMES_tilde_star_indirect(xtab,ytab, k, taunp)
  #CI_tilde:
  LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
  UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
  
  # QMES:
  QES[i] <- QMES_hat_star_direct(xtab,ytab, k, taunp)
  # CI:
  LB_q[i] <- QES[i] - z * log(k/(n*(1/n))) * QES[i] * gamm/sqrt(k)
  UB_q[i] <- QES[i] + z * log(k/(n*(1/n))) * QES[i] * gamm/sqrt(k)
}

#save(kk, n,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, LB_hat, UB_hat, QES, LB_q, UB_q,  file="/Users/.../RDatasets//JPM_MES.RData")


  
  
  #_______________________________
  #
  #   4. Berkshire Hathaway Inc. (BRK-A)
  #       
  #_______________________________ 
# LOAD THE DATA:
load("/Users/.../RDatasets//BRKA_weekly_returns.RData")

n <- length(xtab)

##grid of values of "k":
kl = 1 
ku = 131 # .25*522
kk = kl:ku 
nk = length(kk)

##estreme level:
taunp <- 1-1/n

##Initialization of MES estimates:
gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate of X
XES_hat = cbind(rep(0, nk))     #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
XES_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{XES}}^{\star}_{p_n}(alpha)$
QES = cbind(rep(0, nk))  # usual Weissman quantile estimator
# CIs:
LB_tilde <- cbind(rep(0, nk))
UB_tilde <- cbind(rep(0, nk))
LB_hat <- cbind(rep(0, nk))
UB_hat <- cbind(rep(0, nk))
LB_q <-  cbind(rep(0, nk)) 
UB_q <-  cbind(rep(0, nk))   

##Calculation of MES estimates:
for (i in 1:nk)
{ 
  #Sample fraction:        	
  k <- kk[i]
  
  ## BR-Hill gammma estimate of X:        	         	     
  #gamm  <- Hill_br(xtab, k)
  ## Hill gammma estimate of X:  
  gamm  <- Hill(xtab, k)
  gam[i] <- gamm
  
  # XMES direct $\widehat{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_hat[i] <- XMES_hat_star_direct(xtab,ytab, k, taunp)
  #CI_hat:
  z <- 1.959964 
  LB_hat[i] <- XES_hat[i] - z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k)
  UB_hat[i] <- XES_hat[i] + z * log(k/(n*(1/n))) * XES_hat[i] * gamm/sqrt(k)
  
  # XMES indirect $\widetilde{\textrm{XMES}}^{\star}_{p_n=1-1/n}$:            
  XES_tilde[i] <- XMES_tilde_star_indirect(xtab,ytab, k, taunp)
  #CI_tilde:
  LB_tilde[i] <- XES_tilde[i] - z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
  UB_tilde[i] <- XES_tilde[i] + z * log(k/(n*(1/n))) * XES_tilde[i] * gamm/sqrt(k)
  
  # QMES:
  QES[i] <- QMES_hat_star_direct(xtab,ytab, k, taunp)
  # CI:
  LB_q[i] <- QES[i] - z * log(k/(n*(1/n))) * QES[i] * gamm/sqrt(k)
  UB_q[i] <- QES[i] + z * log(k/(n*(1/n))) * QES[i] * gamm/sqrt(k)
}

#save(kk, n,  gam, XES_hat, XES_tilde, LB_tilde, UB_tilde, LB_hat, UB_hat, QES, LB_q, UB_q,  file="/Users/.../RDatasets//BRKA_MES.RData")


  
#____________________________________________________________________
#
# Figure "extrap_MES_AC.pdf":
#     
#____________________________________________________________________   


#pdf("/Users/.../Figures/extrap_MES_AC.pdf", width=6, height=9)

#require(grid)
grid.newpage()
pushViewport(viewport(layout = grid.layout(2,2)))

define_region = function(row, col){
  viewport(layout.pos.row=row, layout.pos.col=col)
}

# (A) AIG
load("/Users/.../RDatasets//AIG_MES.RData")

df.tilde <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow                                   
df.hat <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red 
df.qes <-data.frame(xxc = (kk/n)*100, yyc = QES, gam)   # solid gray

dd <- ggplot(data=df.qes, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
print(dd+
        geom_line(size = 1.5,data = df.hat, colour = "black", linetype=1)+
        scale_colour_gradientn(name=expression(hat(gamma)[X]), colours=rainbow(7)) + 
        scale_y_continuous(name = "MES")+
     #   scale_x_continuous("Effective sample fraction x 100%")+ 
        scale_x_continuous("")+ 
        #
        geom_line(size = 1.25,data = df.tilde, colour = "hotpink", linetype=1)+
        # 
        labs(title = "(A) American International Group")+ 
        theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                           panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
      vp=define_region(1,1:2))



# (C) JPMorgan Chase
  load("/Users/.../RDatasets//JPM_MES.RData")

df.tilde <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)  # solid hotpink                                     
df.hat <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid black 
df.qes <-data.frame(xxc = (kk/n)*100, yyc = QES, gam)      # rainbow 

df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed hotpink
df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed hotpink

df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed black 
df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed black 

df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed royalblue
df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed royalblue

dd <- ggplot(data=df.qes, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
print(dd+
        geom_line(size = 1.5,data = df.hat, colour = "black", linetype=1)+
        scale_colour_gradientn(name=expression(hat(gamma)[X]), colours=rainbow(7)) + 
        scale_y_continuous(name = "MES")+
        scale_x_continuous("Effective sample fraction x 100%")+ 
        #
        geom_line(size = 1.25,data = df.tilde, colour = "hotpink", linetype=1)+
        # 
        geom_line(size = .8,data = df_LB_tilde, colour = 'hotpink', linetype=2)+
        geom_line(size = .8,data = df_UB_tilde, colour = 'hotpink', linetype=2)+
        #
        geom_line(size = .8,data = df_LB_hat, colour = 'black', linetype=2)+
        geom_line(size = .8,data = df_UB_hat, colour = 'black', linetype=2)+
        #
        geom_line(size = .8,data = df_LB_q, colour = "royalblue", linetype=2)+
        geom_line(size = .8,data = df_UB_q, colour = "royalblue", linetype=2)+
        #
        labs(title = "(C) JPMorgan Chase")+ 
        theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                           panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
      vp=define_region(2,1:2))  

# dev.off()      


#__________________________________
#
# Figure "extrap_MES_BD.pdf":
#     
#__________________________________   


#pdf("/Users/.../Figures/extrap_MES_BD.pdf", width=6, height=9)

#require(grid)
grid.newpage()
pushViewport(viewport(layout = grid.layout(2,2)))

define_region = function(row, col){
  viewport(layout.pos.row=row, layout.pos.col=col)
}


# (B) Citigroup
load("/Users/.../RDatasets//C_MES.RData")

df.tilde <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)    # rainbow
df.hat <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid red
df.qes <-data.frame(xxc = (kk/n)*100, yyc = QES, gam)   # solid gray

dd <- ggplot(data=df.qes, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5)
print(dd+
        geom_line(size = 1.5,data = df.hat, colour = "black", linetype=1)+
        scale_colour_gradientn(name=expression(hat(gamma)[X]), colours=rainbow(7)) +
        scale_y_continuous(name = "MES")+
      #  scale_x_continuous("Effective sample fraction x 100%")+
        scale_x_continuous("")+
        #
        geom_line(size = 1.25,data = df.tilde, colour = "hotpink", linetype=1)+
        #
        labs(title = "(B) Citigroup")+
        theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                           panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),
      vp=define_region(1,1:2))


# (D) Berkshire Hathaway
load("/Users/.../RDatasets//BRKA_MES.RData")

df.tilde <-data.frame(xxc = (kk/n)*100, yyc = XES_tilde, gam)  # solid hotpink                                     
df.hat <-data.frame(xxc = (kk/n)*100, yyc = XES_hat, gam)      # solid black 
df.qes <-data.frame(xxc = (kk/n)*100, yyc = QES, gam)      # rainbow 

df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed hotpink
df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed hotpink

df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed black 
df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed black 

df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed royalblue
df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed royalblue

dd <- ggplot(data=df.qes, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
print(dd+
        geom_line(size = 1.5,data = df.hat, colour = "black", linetype=1)+
        scale_colour_gradientn(name=expression(hat(gamma)[X]), colours=rainbow(7)) + 
        scale_y_continuous(name = "MES")+
        scale_x_continuous("Effective sample fraction x 100%")+ 
        #
        geom_line(size = 1.25,data = df.tilde, colour = "hotpink", linetype=1)+
        # 
        geom_line(size = .8,data = df_LB_tilde, colour = 'hotpink', linetype=2)+
        geom_line(size = .8,data = df_UB_tilde, colour = 'hotpink', linetype=2)+
        #
        geom_line(size = .8,data = df_LB_hat, colour = 'black', linetype=2)+
        geom_line(size = .8,data = df_UB_hat, colour = 'black', linetype=2)+
        #
        geom_line(size = .8,data = df_LB_q, colour = "royalblue", linetype=2)+
        geom_line(size = .8,data = df_UB_q, colour = "royalblue", linetype=2)+
        #
        labs(title = "(D) Berkshire Hathaway")+ 
        theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                           panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),       
        vp=define_region(2,1:2))   

# dev.off()        



 #______________________________________________________________________________
 #
 #   TABLE 1.1
 #
 #   Table~\ref{tab:final_estimates}
 #   Selecting the final pointwise estimates:
 #       
 #______________________________________________________________________________
 
 # 1. Weissman + QES estimates -------------------------------------------------
 
 # (A) china_storm
 load("/Users/.../RDatasets//china_storm_ES.RData")
  
 k.opt = ceiling(0.11*166)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(qes_hat[k.opt])
 c(qes_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (B) us_torn
 load("/Users/.../RDatasets//us_torn_ES.RData")

 k.opt = ceiling(0.11*243)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(qes_hat[k.opt])
 c(qes_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (C) AIG
 load("/Users/.../RDatasets//AIG_ES.RData")
 
 (k.opt = ceiling(0.16*522))
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(qes_hat[k.opt])
 c(qes_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 

 # (D) Market index
 load("/Users/.../RDatasets//Index_ES.RData")
 
 (k.opt = ceiling(0.08*522))
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(qes_hat[k.opt], LB_hat[k.opt], UB_hat[k.opt])
 c(qes_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 
 # 2. XES estimates ------------------------------------------------------------
 
 # (A) china_storm
 load("/Users/.../RDatasets//china_storm_XES.RData")
 
 k.opt = ceiling(0.11*166)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(XES_hat[k.opt])
 c(XES_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (B) us_torn
 load("/Users/.../RDatasets//us_torn_XES.RData")
 
 #k.opt = ceiling(0.12*243)
 k.opt = ceiling(0.11*243)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(XES_hat[k.opt])
 c(XES_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (C) AIG
 load("/Users/.../RDatasets//AIG_XES.RData")
 
 (k.opt = ceiling(0.16*522))
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(XES_hat[k.opt])
 c(XES_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (D) Market index
 load("/Users/.../RDatasets//Index_XES.RData")
 
 (k.opt = ceiling(0.08*522))
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(XES_hat[k.opt], LB_hat[k.opt], UB_hat[k.opt])
 c(XES_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 
# 3. Xtremile estimates ------------------------------------------------------------
 
 # (A) china_storm
 load("/Users/.../RDatasets//china_storm_x.RData")
 
 k.opt = ceiling(0.11*166)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(x_hat[k.opt])
 c(x_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (B) us_torn
 load("/Users/.../RDatasets//us_torn_x.RData")
 
 #k.opt = ceiling(0.12*243)
 k.opt = ceiling(0.11*243)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(x_hat[k.opt])
 c(x_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (C) AIG
 load("/Users/.../RDatasets//AIG_x.RData")
 
 k.opt = ceiling(0.16*522)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(x_hat[k.opt])
 c(x_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (D) Market index
 load("/Users/.../RDatasets//Index_x.RData")
 
 k.opt = ceiling(0.08*522)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(x_hat[k.opt], LB_hat[k.opt], UB_hat[k.opt])
 c(x_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 
   
# 4. Xpectile estimates ------------------------------------------------------------
 
 # (A) china_storm
 load("/Users/.../RDatasets//china_storm_e.RData")

  k.opt = ceiling(0.11*166)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(e_hat[k.opt])
 c(e_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 par(mfrow=c(1,1))
 par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
 # q.Weissman
 plot((kk/n)*100, q.Weissman, type = 'l', col='royalblue', lwd=3, main = expression(""), las=1, cex.lab=1.6, cex.axis=1.6,
      cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", ylim=c(min(LB_tilde),max(UB_tilde))) #, xlim=c(0,60)) #ylim=c(0,1.5) , xlim=c(0,60)) # , xlim=c(0,40))

 # expectile direct
 lines((kk/n)*100, e_hat, lty=1, col='red', lwd=2)
 
 # expectile indirect
 lines((kk/n)*100, e_tilde, lty=1, col='orange', lwd=2)
 
 lines((kk/n)*100, LB_tilde, lty=2, col='orange', lwd=2)
 lines((kk/n)*100, UB_tilde, lty=2, col='orange', lwd=2)
 
 # selected k
 abline(v=(k.opt/n)*100, lty=3, col='magenta', lwd=3)


 
 # (B) us_torn
 load("/Users/.../RDatasets//us_torn_e.RData")
 
 k.opt = ceiling(0.11*243)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(e_hat[k.opt])
 c(e_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 

 par(mfrow=c(1,1))
 par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
 # q.Weissman
 plot((kk/n)*100, q.Weissman, type = 'l', col='royalblue', lwd=3, main = expression(""), las=1, cex.lab=1.6, cex.axis=1.6,
      cex.main=1.6, bty="l", xlab="Effective sample fraction x 100%", ylab="", ylim=c(min(LB_tilde),max(UB_tilde))) #, xlim=c(0,60)) #ylim=c(0,1.5) , xlim=c(0,60)) # , xlim=c(0,40))
 
 # expectile direct
 lines((kk/n)*100, e_hat, lty=1, col='red', lwd=2)
 
 # expectile indirect
 lines((kk/n)*100, e_tilde, lty=1, col='orange', lwd=2)
 
 lines((kk/n)*100, LB_tilde, lty=2, col='orange', lwd=2)
 lines((kk/n)*100, UB_tilde, lty=2, col='orange', lwd=2)
 
 # selected k
 abline(v=(k.opt/n)*100, lty=3, col='magenta', lwd=3)
 #abline(h=q.Weissman[k.opt], lty=2, col='magenta', lwd=3)
 
 
 
 # (C) AIG
 load("/Users/.../RDatasets//AIG_e.RData")
 
 k.opt = ceiling(0.16*522)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(e_hat[k.opt])
 c(e_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 
 
 # (D) Market index
 load("/Users/.../RDatasets//Index_e.RData")
 
 k.opt = ceiling(0.08*522)
 c(q.Weissman[k.opt], LB_q[k.opt], UB_q[k.opt])
 c(e_hat[k.opt], LB_hat[k.opt], UB_hat[k.opt])
 c(e_tilde[k.opt], LB_tilde[k.opt], UB_tilde[k.opt])
 

 
 ###############################################################################
 #
 #       FIGURE 1.9
 #
 #       Figure in the discussion section
 #
 ###############################################################################
 
 #_______________________________
 #
 #   Basic extrapolated expectile estimates
 #   Market index weekly loss returns
 #       
 #_______________________________ 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//JPM_weekly_returns.RData")

 n <- length(Yw)
 Yn = max(Yw)
 ysort=sort(Yw)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(Yw, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(Yw, k, taunp)
   #CI_hat:
   z <- 1.959964 
   LB_hat[i] <- e_hat[i] - z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k)
   UB_hat[i] <- e_hat[i] + z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k) 
   
   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(Yw, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(Yw, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
 # save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//MIndex_e.RData")
 
 
 
 
 #_______________________________
 #
 #   BR extrapolated expectile estimates
 #   Market index weekly loss returns
 #       
 #_______________________________ 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//JPM_weekly_returns.RData")

 n <- length(Yw)
 Yn = max(Yw)
 ysort=sort(Yw)   
 
 ##grid of values of "k":
 kl = 1
 ku = 131 # .25*522
 kk = kl:ku
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk))
 UB_q <-  cbind(rep(0, nk))
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 {
   #Sample fraction:
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:
   gamm  <- Hill_br(Yw, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:
   br.xpectile <- CIextExpect(X=Yw, k=k, tau=taunp, method = "direct")
   e_hat[i] <- as.numeric(br.xpectile$Point_estimate)
   #CI_hat:
   LB_hat[i] <- as.numeric(br.xpectile$Lower_bound)
   UB_hat[i] <- as.numeric(br.xpectile$Upper_bound)
   
   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:
   br.xpectile.ind <- CIextExpect(X=Yw, k=k, tau=taunp, method = "indirect")
   e_tilde[i] <- as.numeric(br.xpectile.ind$Point_estimate)
   #CI_tilde:
   LB_tilde[i] <- as.numeric(br.xpectile.ind$Lower_bound)
   UB_tilde[i] <- as.numeric(br.xpectile.ind$Upper_bound)
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(Yw, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)
 }
 
 #save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//MIndex_eBR.RData")
 
 

 #_______________________________
 #
 #   Basic extrapolated expectile estimates
 #   JPMorgan Chase (JPM)
 #       
 #_______________________________ 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//JPM_weekly_returns.RData")

 n <- length(xtab)
 Yn = max(xtab)
 ysort=sort(xtab)   
 
 ##grid of values of "k":
 kl = 1 
 ku = 131 # .25*522
 kk = kl:ku 
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk)) 
 UB_q <-  cbind(rep(0, nk))   
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 { 
   #Sample fraction:        	
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:        	         	     
   gamm  <- Hill_br(xtab, k)
   gam[i] <- gamm
   
   # XES direct $\widehat{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_hat[i] <- xpectile_hat_star_direct(xtab, k, taunp)
   #CI_hat:
   z <- 1.959964 
   LB_hat[i] <- e_hat[i] - z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k)
   UB_hat[i] <- e_hat[i] + z * log(k/(n*(1/n))) * e_hat[i] * gamm/sqrt(k) 
   
   # XES indirect $\widetilde{\textrm{XES}}^{\star}_{p_n=1-1/n}$:            
   e_tilde[i] <- xpectile_tilde_star_indirect(xtab, k, taunp)
   #CI_tilde:
   LB_tilde[i] <- e_tilde[i] - z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k)
   UB_tilde[i] <- e_tilde[i] + z * log(k/(n*(1/n))) * e_tilde[i] * gamm/sqrt(k) 
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k) 
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)       
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//JPM_e.RData")
 
 #_______________________________
 #
 #   BR extrapolated expectile estimates
 #   JPMorgan Chase (JPM)
 #       
 #_______________________________ 
 # LOAD THE DATA:
 load("/Users/.../RDatasets//JPM_weekly_returns.RData")

 n <- length(xtab)
 Yn = max(xtab)
 ysort=sort(xtab)   
 
 ##grid of values of "k":
 kl = 1
 ku = 131 # .25*522
 kk = kl:ku
 nk = length(kk)
 
 ##estreme level:
 taunp <- 1-1/n
 
 ##Initialization of ES estimates:
 line_max = cbind(rep(0, nk))    #Sample maximum
 gam =  cbind(rep(0, nk))        #BR-Hill gammma estimate
 e_hat = cbind(rep(0, nk))     #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 e_tilde = cbind(rep(0, nk))   #$\widehat{\textrm{x}}^{\star}_{p_n}(alpha)$
 q.Weissman = cbind(rep(0, nk))  # usual Weissman quantile estimator
 # CIs:
 LB_tilde <- cbind(rep(0, nk))
 UB_tilde <- cbind(rep(0, nk))
 LB_hat <- cbind(rep(0, nk))
 UB_hat <- cbind(rep(0, nk))
 LB_q <-  cbind(rep(0, nk))
 UB_q <-  cbind(rep(0, nk))
 
 ##Calculation of ES estimates:
 for (i in 1:nk)
 {
   #Sample fraction:
   k <- kk[i]
   
   #Sample maximum:
   line_max[i] <- Yn
   
   #BR-Hill gammma estimate:
   gamm  <- Hill_br(xtab, k)
   gam[i] <- gamm
   
   # x direct $\widehat{\textrm{x}}^{\star}_{p_n=1-1/n}$:
   br.xpectile <- CIextExpect(X=xtab, k=k, tau=taunp, method = "direct")
   e_hat[i] <- as.numeric(br.xpectile$Point_estimate)
   #CI_hat:
   LB_hat[i] <- as.numeric(br.xpectile$Lower_bound)
   UB_hat[i] <- as.numeric(br.xpectile$Upper_bound)
   
   # x indirect $\widetilde{\textrm{x}}^{\star}_{p_n=1-1/n}$:
   br.xpectile.ind <- CIextExpect(X=xtab, k=k, tau=taunp, method = "indirect")
   e_tilde[i] <- as.numeric(br.xpectile.ind$Point_estimate)
   #CI_tilde:
   LB_tilde[i] <- as.numeric(br.xpectile.ind$Lower_bound)
   UB_tilde[i] <- as.numeric(br.xpectile.ind$Upper_bound)
   
   # Weissman quantile estimator:
   q.Weissman[i] <- weissman_quantile(xtab, k, taunp)
   # CI:
   LB_q[i] <- q.Weissman[i] - z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)
   UB_q[i] <- q.Weissman[i] + z * log(k/(n*(1/n))) * q.Weissman[i] * gamm/sqrt(k)
 }
 
# save(kk, n, line_max,  gam, e_hat, e_tilde, LB_tilde, UB_tilde, q.Weissman, LB_q, UB_q, LB_hat, UB_hat, file="/Users/.../RDatasets//JPM_eBR.RData")
 
 #____________________________________________________________________
 #
 # Figure "extrap_EBR_discussion_AC.pdf":
 #     
 #____________________________________________________________________   
 
 
 # pdf("/Users/.../Figures/extrap_EBR_discussion_AC.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (A) MIndex : Basic extrapolated expectile estimates
 load("/Users/.../RDatasets//MIndex_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
       #  scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .9,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .8,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .8,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .8,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .8,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .8,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .8,data = df_UB_q, colour = "black", linetype=2)+
         labs(title = "(A) Market index: basic estimates")+
         coord_cartesian(ylim=c(0,0.4),xlim=c(NA,NA))+
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),
       vp=define_region(1,1:2))
 
 
 # (C) JPM : Basic extrapolated expectile estimates
 load("/Users/.../RDatasets//JPM_e.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .9,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .8,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .8,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .8,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .8,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .8,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .8,data = df_UB_q, colour = "black", linetype=2)+
         labs(title = "(C) JPMorgan Chase: basic estimates")+
         coord_cartesian(ylim=c(0,0.8),xlim=c(NA,NA))+
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),
       vp=define_region(2,1:2))   
 
#  dev.off()      
 
 
 #__________________________________
 #
 # Figure "extrap_EBR_discussion_BD.pdf":
 #     
 #__________________________________   
 
 
 #pdf("/Users/.../Figures/extrap_EBR_discussion_BD.pdf", width=6, height=9)
 
 #require(grid)
 grid.newpage()
 pushViewport(viewport(layout = grid.layout(2,2)))
 
 define_region = function(row, col){
   viewport(layout.pos.row=row, layout.pos.col=col)
 }
 
 # (B) MIndex : BR extrapolated expectile estimates
 load("/Users/.../RDatasets//MIndex_eBR.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
     #    scale_x_continuous("Effective sample fraction x 100%")+ 
         scale_x_continuous("")+ 
         #
         geom_line(size = .9,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .8,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .8,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .8,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .8,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .8,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .8,data = df_UB_q, colour = "black", linetype=2)+
         labs(title = "(B) Market index: bias-reduced estimates")+
         coord_cartesian(ylim=c(0,0.4),xlim=c(NA,NA))+
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),
       vp=define_region(1,1:2))
 
 # (D) JPM : BR extrapolated expectile estimates
 load("/Users/.../RDatasets//JPM_eBR.RData")
 
 dfff <-data.frame(xxc = (kk/n)*100, yyc = line_max)         # dashed magenta                    
 dff <-data.frame(xxc = (kk/n)*100, yyc = e_tilde, gam)    # rainbow                                   
 df5 <-data.frame(xxc = (kk/n)*100, yyc = e_hat, gam)      # solid red 
 df6 <-data.frame(xxc = (kk/n)*100, yyc = q.Weissman, gam)   # solid black 
 
 df_LB_tilde <-data.frame(xxc = (kk/n)*100, yyc = LB_tilde, gam) # dashed royalblue
 df_UB_tilde <-data.frame(xxc = (kk/n)*100, yyc = UB_tilde, gam) # dashed royalblue
 
 df_LB_hat <-data.frame(xxc = (kk/n)*100, yyc = LB_hat, gam) # dashed red
 df_UB_hat <-data.frame(xxc = (kk/n)*100, yyc = UB_hat, gam) # dashed red
 
 df_LB_q <-data.frame(xxc = (kk/n)*100, yyc = LB_q, gam) # dashed black
 df_UB_q <-data.frame(xxc = (kk/n)*100, yyc = UB_q, gam) # dashed black
 
 dd <- ggplot(data=dff, aes(xxc, yyc,col=gam)) + geom_line(size = 1.5) 
 print(dd+geom_line(size = 1,data = dfff, colour = "magenta", linetype=2)+
         scale_colour_gradientn(name=expression(hat(gamma)[tau[n]]), colours=rainbow(7)) + 
         scale_y_continuous(name = "Expectile")+
         scale_x_continuous("Effective sample fraction x 100%")+ 
         #
         geom_line(size = .9,data = df5, colour = "red", linetype=1)+
         # 
         geom_line(size = 1,data = df6, colour = "gray", linetype=1)+
         # 
         geom_line(size = .8,data = df_LB_hat, colour = "red", linetype=2)+
         geom_line(size = .8,data = df_UB_hat, colour = "red", linetype=2)+  
         geom_line(size = .8,data = df_LB_tilde, colour = 'royalblue', linetype=2)+
         geom_line(size = .8,data = df_UB_tilde, colour = 'royalblue', linetype=2)+
         #
         # geom_line(size = .6,data = df_LB_q, colour = "black", linetype=2)+
         # geom_line(size = .6,data = df_UB_q, colour = "black", linetype=2)+
         labs(title = "(D) JPMorgan Chase: bias-reduced estimates")+
         coord_cartesian(ylim=c(0,0.8),xlim=c(NA,NA))+
         theme_bw() + theme(panel.border = element_blank(), panel.grid.major = element_blank(),
                            panel.grid.minor = element_blank(), axis.line = element_line(colour = "black"), plot.title = element_text(size=16, face="bold"), axis.title.x = element_text(size=15), axis.title.y = element_text(size=15)),
       vp=define_region(2,1:2))   
 
 # dev.off()      
 
 
 
 
 ################################################################################
 ###
 ### FIGURE 1.7
 ###
 ################################################################################
   
   require(cubature)
 
 my_c <- function(u, theta){
   exp(-((-log(u[1]))^(theta) + (-log(u[2]))^(theta))^(1/theta))
 }
 
 cdfX <- function(x){
   exp(-x^(-4)) * as.numeric(x>0)
 }
 
 tailcdfX <- function(x){
   1 - exp(-x^(-4)) * as.numeric(x>0)
 }
 
 cdfY <- function(x){
   (1 - x^(-4))*as.numeric(x>1)
 }
 
 quantY <- function(a){
   (1 - a)^(-1/4)
 }
 
 cdf <- function(x, theta){
   my_c(c(cdfX(x[1]), cdfY(x[2])), theta)
 }
 
 
 tailcdf <- function(x, t, theta){
   1 + cdf(c(x, t), theta) - cdfX(x) - cdfY(t)
 }
 
 tailcdf(3, t = 2, theta = 2)
 (cubintegrate(f = tailcdf, lower = 10^(-10), upper = Inf, t = 2, theta = 2)$integral)/(1 - cdfY(2))
 cubintegrate(f = tailcdfX, lower = 10^(-10), upper = Inf)
 
 # function for one value of t and one value of theta
 my_f <- function(x, y) {
   my_t <- quantY(x)
   res <- (cubintegrate(f = tailcdf, lower = 10^(-6), upper = Inf, 
                        t = my_t, theta = y)$integral)/
     (1 - cdfY(my_t))
   return(res)
 }
 
 # vectorized function
 my_f_vectorial <- function(x, y) {
   mapply(my_f, x, y)
 }
 
 level <- seq(0.5, 0.99, by = 0.01)
 s <- seq(1, 10, by = 0.1)
 res <- outer(level, s, my_f_vectorial)
 
 #########################################################
 ####  2D representation
 
 # contour plot using lattice graphics and R Color Brewer
 library(RColorBrewer) #for brewer.pal()
 
 # pdf(file = "my_contours.pdf", width = 8, height = 8)
 filled.contour(level, s, res, 
                levels = seq(1, 4.5, by = 0.5), 
                nlevels = 7, col = brewer.pal(7, "YlOrRd"), xlab = 'Quantile level', ylab = 'Theta parameter',
                plot.axes = {
                  axis(1)
                  axis(2)
                  contour(level, s, res, add = TRUE, lwd = 0.9)
                })
 # dev.off()
 
 # version ggplot
 gdat <- data.frame(x = rep(level, times = length(s)),
                    y = rep(s, each = length(level)),
                    z = as.vector(res))
 library(ggplot2)
 library(metR)
 ggplot(gdat, aes(x = x, y = y)) + 
   geom_contour_fill(aes(z = z)) +
   geom_contour(aes(z = z), color = "black") +
   geom_text_contour(aes(z = z)) +
   xlab('Quantile level') + 
   ylab('Theta parameter') +
   labs(fill = "")
 ggsave("my_contours_2.pdf", width = 8, height = 8)
 
 
 #########################################################
 ####  3D representation
 
 
 # pdf(file = "persp.pdf", width = 8, height = 8)
 par(oma = c(0,0 ,0, 0), mar = c(0, 3.5, 0, 5))
 persp(level, s, res, theta = -40, phi = 12, shade = 0.15, col = "lightblue", 
       expand = 0.75, r = 1, ltheta = 15, ticktype = "detailed", lwd = 0.1,
       nticks = 5, xlab = 'Quantile level', ylab = 'Theta parameter', zlab = "")
 # dev.off()   
 
 
 
 ###############################################################################
 #
 #       FIGURE 1.10
 #
 ###############################################################################
 evi=seq(.001,.499,by=.001)
 
 variance_ES_empirical=2*evi^2*(1-evi)/(1-2*evi)
 variance_ES_quantilebased=evi^2*(1+1/(1-evi)^2)
 variance_expectile_empirical=2*evi^3/(1-2*evi)
 variance_expectile_quantilebased=evi^2*(1+((1-evi)^(-1)-log(evi^(-1)-1))^2)
 variance_extremile_empirical=rep(NA,length(evi))
 
 for (i in (1:length(evi))){
   variance_extremile_empirical[i]=(1/gamma(1-evi[i]))*(evi[i])^2*log(2)*2*integrate(function(t){pgamma(t,1-evi[i])*exp(-t)*t^(-evi[i]-1)}, 10^(-10), Inf)$value
 }
 
 variance_extremile_quantilebased=evi^2*(1+(log(log(2))-digamma(1-evi))^2)
 
 
 # pdf("/Users/.../Figures/asymptotic_var_comparison.pdf", width=11, height=6)
 par(mfrow=c(1,1))
 par(mai=c(.65,.68,.35,.1), mgp=c(2.1,.6,0))
 
 plot(evi,variance_ES_empirical/evi^2,type="l",col="red", lwd=2, ylim=c(0,5), main = "Comparison of the asymptotic variances for intermediate estimators",
      xlab="Value of the extreme value index",ylab="Ratio of asymptotic variances", 
      las=1, cex.lab=1.6, cex.axis=1.6,
      cex.main=1.6, bty="l")
 lines(evi,variance_ES_quantilebased/evi^2,col="red",lty=2, lwd=2)
 lines(evi,variance_expectile_empirical/evi^2,col="blue", lwd=2)
 lines(evi,variance_expectile_quantilebased/evi^2,col="blue", lty=2, lwd=2)
 lines(evi,variance_extremile_empirical/evi^2,col="orange", lwd=2)
 lines(evi,variance_extremile_quantilebased/evi^2,col="orange",lty=2, lwd=2)
 abline(h=1,lty=3, lwd=1.5)
 
#  dev.off()  
 
 
 
 
 
 
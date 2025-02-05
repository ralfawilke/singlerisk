rm(list = ls())

# This R code replicates the results of the numerical analysis in 
# Lo, S.M.S. and Wilke, R.A. (2025): "Accelerated failure time analysis for industrial life modelling in presence of unknown dependent censoring", Quality Engineering

# Sample estimation code for the AFT model applied to the radio data by Mendehall and Hader (1958): 
# Estimation of parameters of mixed exponentially distributed failure time distributions from censored life test data. Biometrika, 45, 504-520.


###########################################################################
con   = c(16,224,16,80,128,168,144,176,176,568,392,576,128,56,112,160,384,600,40,416,
          408,384,256,246,184,440,64,104,168,408,304,16,72,8,88,160,48,168,80,512,
          208,194,136,224,32,504,40,120,320,48,256,216,168,184,144,224,488,304,40,160,
          488,120,208,32,112,288,336,256,40,296,60,208,440,104,528,384,264,360,80,96,
          360,232,40,112,120,32,56,280,104,168,56,72,64,40,480,152,48,56,328,192,
          168,168,114,280,128,416,392,160,144,208,96,536,400,80,40,112,160,104,224,336,
          616,224,40,32,192,126,392,288,248,120,328,464,448,616,168,112,448,296,328,56,
          80,72,56,608,144,408,16,560,144,612,80,16,424,264,256,528,56,256,112,544,
          552,72,184,240,128,40,600,96,24,184,272,152,328,480,96,296,592,400,8,280,
          72,168,40,152,488,480,40,576,392,552,112,288,168,352,160,272,320,80,296,248,
          184,264,96,224,592,176,256,344,360,184,152,208,160,176,72,584,144,176)
uncon = c(368,136,512,136,472,96,144,112,104,104,344,246,72,80,312,24,128,304,16,320,
          560,168,120,616,24,176,16,24,32,232,32,112,56,184,40,256,160,456,48,24,
          200,72,168,288,112,80,584,368,272,208,144,208,114,480,114,392,120,48,104,272,
          64,112,96,64,360,136,168,176,256,112,104,272,320,8,440,224,280,8,56,216,
          120,256,104,104,8,304,240,88,248,472,304,88,200,392,168,72,40,88,176,216,
          152,184,400,424,88,152,184)
cen   = rep(630,44)

t.event = c(con,uncon,cen)
event1  = c(rep(1,length(con)),rep(0,length(uncon)),rep(0,length(cen))) #dummy for confirmed failure
event2  = c(rep(0,length(con)),rep(1,length(uncon)),rep(0,length(cen))) #dummy for unconfirmed failure

###############################################

# Set relevant parameters under ##### SETUP #####

#install.packages("copula")
#install.packages(c("survival", "survminer"))
#install.packages("scatterplot3d")
#install.packages("cmprsk")
#install.packages("pastecs")
#install.packages("plyr") 

library(pastecs)
library(cmprsk)
library(timereg)
library(MALDIquant)
library(copula)
library(survival)
library(plyr)
library(dplyr)
library(readxl)
library(latex2exp)


########## SETUP  ##########

model = "llog" ## choose the model "expo" "weib" ""llog"
ecge = "clayton" ## choose the model "clayton" "frank" "gumbel"
t<-t.event #duration variable 
delw = 2-event1  # input the name of risk indicator: risk1=1, risk2=2,censored=0
I<-which(event1+event2==0)
cen<- 630 # fixed censoring point
delw[I]=0
rep = 500  # bootstrap sample 

#Set range of tau for cge for numerical minimisation of the variance criterion in theta:
# for ecge1
c_l=-0.9
c_u=0.85

#Set range of tau for cge for OPTIONAL plots:
taugd <-c(seq(c_l,c_u,0.05))

############################
dat0 <- data.frame(t,delw) # data frame containing all relevant data
n <- nrow(dat0)
k <- 2 # number of risks
tqlim <- 1 # when plotting the graph, max is quantile of tqlim

# to define cge, we define some functions regarding the copula generator
invpsiclayton <- function(s, tau){  # inverse copula generator of clayton
  if (tau==0){
    u <- exp(-s)
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    u <- (theta*s+1)^(-1/theta)
  }
  return(u)
}
dpsiclayton <- function(s, tau){  # derivative of copula generator of clayton
  if (tau==0){
    u<--1/s
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    u <- -s^(-1-theta)
  }
  return(u)
}
dinvpsiclayton <- function(s, tau){  # derivative of inverse generator of clayton
  if (tau==0){
    u<- -exp(-s)
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    u <- -(1+theta*s)^(-1-1/theta)
  } 
  return(u)
}
psiclayton<-function(s,tau){ # copula generator of clayton
  if (tau==0){
    
    u<- -log(s)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    
    u<-(s^(-theta)-1)/theta
  }
  return(u)
}
cgeclayton <- function(q1, q2, f, dt, tau){ # cge using clayton
  
  if (tau==0){
    u<- exp(-cumsum(f/(1-q1-q2)*dt))
  }
  if (tau!=0){
    
    u<- invpsiclayton(-cumsum(dpsiclayton(1-q1-q2,tau)*f*dt), tau)
  }
  return(u)
}
invpsifrank <- function(s, tau){  # inverse copula generator of frank
  if (tau==0){
    u <- exp(-s)
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("frank"), tau)
    u <- -log(1+exp(-s)*(exp(-theta)-1))/theta
    u[is.na(u)] <- 1e-16
  }
  return(u)
}

dpsifrank <- function(s, tau){  # derivative of copula generator of frank
  s[s < 0] <- 1e-16
  if (tau==0){
    u<--1/s
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("frank"), tau)
    u <- -theta/(exp(theta*s)-1)
  }
  return(u)
}


psifrank<-function(s,tau){ # copula generator of frank
  if (tau==0){
    
    u<- -log(s)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("frank"), tau)
    
    u<- -log((exp(-theta*s)-1)/(exp(-theta)-1))
  }
  return(u)
}

cgefrank <- function(q1, q2, f, dt, tau){ # cge using frank
  
  if (tau==0){
    u<- exp(-cumsum(f/(1-q1-q2)*dt))
  }
  
  if (tau!=0){
    
    u<- invpsifrank(-cumsum(dpsifrank(1-q1-q2,tau)*f*dt), tau)
    
  }
  return(u)
}

invpsigumbel <- function(s, tau){  # inverse copula generator of gumbel
  if (tau==0){
    u <- exp(-s)
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("gumbel"), tau)
    u <- exp(-s^(1/theta))
  }
  return(u)
}

psigumbel<-function(s,tau){ # copula generator of gumbel
  if (tau==0){
    
    u<- -log(s)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("gumbel"), tau)
    
    u<- (-log(s))^(theta)
  }
  return(u)
}

dpsigumbel <- function(s, tau){  # derivative of copula generator of gumbel
  s[s < 0] <- 1e-16
  if (tau==0){
    u<- -1/s
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("gumbel"), tau)
    u <- -theta*(-log(s))^(theta-1)/s
  }
  return(u)
}


cgegumbel <- function(q1, q2, f, dt, tau){ # cge using frank
  
  if (tau==0){
    u<- exp(-cumsum(f/(1-q1-q2)*dt))
  }
  
  if (tau!=0){
    
    u<- invpsigumbel(-cumsum(dpsigumbel(1-q1-q2,tau)*f*dt), tau)
    
  }
  return(u)
}

# we define the function for log-logistic distribution with covariate z
llogistic <- function(t, a, b){  # survival function
  u<-(1+(t/a)^(b))^(-1)
}
## b = 1/sigma, a = 1/lambda
dllogistic <- function(t, a, b){ # hazard function
  u <- ((b/a)*(t/a)^(b-1))/(1+(t/a)^b)
}
invllogistic <- function(u, a, b){
  t = a*(u^(-1)-1)^(1/b)
}
# we define the function for weibull distribution with covariate z
weib <- function(t, a, b){  # survival function
  u<-exp(-(a*t)^b)
}
dweib <- function(t, a, b){ # hazard function
  u <- a^b*b*t^(b-1)*exp(-(a*t)^b)
}
invweib <- function(u, a, b){
  t = (-log(u)/a^b)^(1/b)
}
# we define the function for expo distribution with covariate z
expo <- function(t, a){  # survival function
  u<-exp(-a*t)
}
dexpo <- function(t, a){ # hazard function
  u <- a*exp(-a*t)
}

invexpo <- function(u, a){
  t = -log(u)/a
}

##################
# objective function
#################

opttau <- function(etau){
  # compute the estimated CGE
  
  datQu<-datQ
  
  datQu<-invisible(datQu %>% select(-2))
  
  datQu<-as.data.frame(unique(datQu)) # for unique t
  
  if (ecge == "clayton") {
    ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  if (ecge == "frank") {
    ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  if (ecge == "gumbel") {
    ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  
  ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
  ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
  
  #exclude observations with S_CGE=0
  datQu<-datQu %>% filter(ecgewu > 0) 
  
  #inflate row length of ecgewu and 1u back to all observations
  #create matrices of 0
  ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
  
  
  for(i in 1:length(ecgewu)){
    I<-which(datQ[,1]==datQu[i,1])
    ecgew[I]<-ecgewu[i]
  }
  
  # estimate alpha using regression
  datQ<- data.frame(datQ,ecgew)
  y <- log(datQ$t) # tranform t to log(t)
  y[which(is.infinite(y))]<-NaN
  
  if (model == "expo") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    y<-y-lcge
    #datlm<-data.frame(y,z1) # run regression need a data frame
    fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
    eaw<-exp(-fit$coefficients[[1]])
    eSemiw <- exp(-datQ[,1]*eaw)
  }
  if (model == "weib") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- 1/fit$coefficients[[2]] # parameter transformation
    eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
    eSemiw <- exp(-(datQ[,1]*eaw)^ebw)  # construct Sj implie by the semimodel
  }
  if (model == "llog") {
    lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- -1/fit$coefficients[[2]] # parameter transformation
    eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
    eSemiw <- 1/(1+(datQ[,1]/eaw)^ebw)
  }
  eSemiw[is.na(eSemiw)] <- Inf  # eSemi has Na at the end of the column, so replace it to -inf
  eSemiw[is.infinite(eSemiw)] <- min(eSemiw)  # replace -inf to max of the column, i.e. Q(infty)
  I<-which(datQ[,1]<cen)
  CvM <- sum((ecgew[I]-eSemiw[I])^2) #  objective function is the mean squared sum error, restrict to below fixed censoring point
  # CvM <- sum((ecgew-eSemiw)^2) #  objective function is the mean squared sum error, unrestricted
  return(CvM)
}


######################
#Estimation
######################
dat <- dat0
summary(dat)
tabulate(delw)

### START OPTIM and search for tau ###
# we need Qj and to estimate CGE.
dat<-dat[order(dat$t),] # sort the data with t

q <-cuminc(dat[,1],dat[,2],cencode=0) #estimate cumulative incidences
tp <-timepoints(q,dat[,1]) # change the time grid to original data point
eQ<-unname(t(tp[[1]])) # combine with t, delta

for(i in 1:dim(eQ)[2]){
  eQ[is.na(eQ[,i]),i] <- -Inf  # Q has Na at the end of the column, so replace it to -inf
  eQ[is.infinite(eQ[,i]),i] <- max(eQ[,i])  # replace -inf to max of the column, i.e. Q(infty)
}

#vectors and matrices with unique time points and estimates
ut<-as.data.frame(unique(dat[,1]))
ut<-rbind(rep(0,1),ut) # add row of zeros as the first row
eQ_1<-rbind(rep(0,1),eQ) # add row of zeros as the first row

dt<-diff(ut[,1],lag=1)  # ti - t_{i-1} 
ef<-diff(eQ_1,lag=1)/dt # first different of Qj = fj: add zero as first observation
#ef[is.na(ef)] <- 0

ut<-as.data.frame(unique(dat[,1])) # unique time points without leading 0

#create matrices of zeros
eQfull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
effull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
dtfull<-matrix(0, 1, nrow = length(dat[,1]))


# create matrices of t, eQ and ef with row dimension equaling the number of observations.
for(i in 1:dim(ut)[1]){
  I<-which(dat[,1]==ut[i,1])
  for(j in 1:k){
    eQfull[I,j]<-eQ[i,j]
    effull[I,j]<-ef[i,j]
  }
  dtfull[I,1]<-dt[i]
}

datQ<-data.frame(dat,eQfull,effull,dtfull) # check the data of Qj



#determine start value for numerical minimisation

f<- rep(NA,length(taugd))
for(i in 1:length(taugd)){
  f[i] <- opttau(taugd[i])
}

I<-which(f==min(f))
startvalue<-taugd[I]

f1<-optim(startvalue, opttau, method=c("Brent"), lower=c_l,upper=c_u)

############################################
### plot of objective function
############################################


#plot objective function for assumed copula & marginal
pdf("H:\\paper\\LoWilke2023\\code\\cvm_criterion.pdf")
plot(taugd, f, type='l',axes=FALSE, xlab=TeX(r'($\tau$)'), ylab="Criterion")
axis(1, taugd)
axis(2)
dev.off()

############################################
### plot of estimated survival
############################################


datQu<-datQ

datQu<-invisible(datQu %>% select(-2))

datQu<-as.data.frame(unique(datQu)) # for unique t

if (ecge == "clayton") {
  ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], f1$par) # estimate of cge Risk1 
  ecgeuu = cgeclayton(datQu[,2],datQu[,3],datQu[,5],datQu[,6], f1$par) # estimate of cge Risk2
  ecgewum09 = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], -0.9) # estimate of cge Risk1 
  ecgewu0 = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0) # estimate of cge Risk1 
  ecgewu09 = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0.9) # estimate of cge Risk1 
}
if (ecge == "frank") {
  ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], f1$par) # estimate of cge Risk 1
  ecgeuu = cgefrank(datQu[,2],datQu[,3],datQu[,5],datQu[,6], f1$par) # estimate of cge Risk 2
  ecgewum09 = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], -0.9) # estimate of cge Risk1 
  ecgewu0 = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0) # estimate of cge Risk1 
  ecgewu09 = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0.9) # estimate of cge Risk1 
}
if (ecge == "gumbel") {
  ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], f1$par) # estimate of cge Risk1
  ecgeuu = cgegumbel(datQu[,2],datQu[,3],datQu[,5],datQu[,6], f1$par) # estimate of cge Risk2
  ecgewum09 = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], -0.9) # estimate of cge Risk1 
  ecgewu0 = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0) # estimate of cge Risk1 
  ecgewu09 = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], 0.9) # estimate of cge Risk1 
}

#Address numerical issues with CGE
ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
ecgeuu[is.na(ecgeuu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgeuu[is.infinite(ecgeuu)] <- min(ecgeuu)  # replace -inf to max of the column, i.e. Q(infty)

ecgewum09[is.na(ecgewum09)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgewum09[is.infinite(ecgewum09)] <- min(ecgewum09)  # replace -inf to max of the column, i.e. Q(infty)
ecgewu0[is.na(ecgewu0)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgewu0[is.infinite(ecgewu0)] <- min(ecgewu0)  # replace -inf to max of the column, i.e. Q(infty)
ecgewu09[is.na(ecgewu09)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgewu09[is.infinite(ecgewu09)] <- min(ecgewu09)  # replace -inf to max of the column, i.e. Q(infty)

#exclude observations with S_CGE=0 or S_CGE=1
datQu<-datQu %>% filter(ecgewu > 0 & ecgewu < 1) 

#inflate row length of ecgewu and 1u back to all observations
#create matrices of 0
ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
ecgeu<-matrix(0, ncol = 1 , nrow = length(dat[,1]))

ecgewm09<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
ecgew0<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
ecgew09<-matrix(0, ncol = 1 , nrow = length(dat[,1]))

for(i in 1:length(ecgewu)){
  I<-which(datQ[,1]==datQu[i,1])
  ecgew[I]<-ecgewu[i]
  ecgeu[I]<-ecgeuu[i]
  
  ecgewm09[I]<-ecgewum09[i]
  ecgew0[I]<-ecgewu0[i]
  ecgew09[I]<-ecgewu09[i]
}

# estimate alpha using regression
datQ<- data.frame(datQ,ecgew)
y <- log(datQ$t) # tranform t to log(t)
y[which(is.infinite(y))]<-NaN

if (model == "expo") {
  lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
  lcge[which(is.infinite(lcge))]<-NaN
  y<-y-lcge
  #datlm<-data.frame(y,z1) # run regression need a data frame
  fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
  eaw<-exp(-fit$coefficients[[1]])
  eS <- exp(-datQ[,1]*eaw)
}
if (model == "weib") {
  lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
  lcge[which(is.infinite(lcge))]<-NaN
  #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
  fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
  ebw <- 1/fit$coefficients[[2]] # parameter transformation
  eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
  eS<- exp(-(datQ[,1]*eaw)^ebw)  # construct Sj implie by the semimodel
}
if (model == "llog") {
  lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
  lcge[which(is.infinite(lcge))]<-NaN
  #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
  fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
  ebw <- -1/fit$coefficients[[2]] # parameter transformation
  eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
  eS <- 1/(1+(datQ[,1]/eaw)^ebw)
}

#Plots of estimated S(t) 

pdf("H:\\paper\\LoWilke2023\\code\\Semipara_surv.pdf")
plot(datQ[,1],eS, type='l', xlab="life-time (in hours)", ylab=TeX(r'($S(t)$)'))
lines(datQ[,1],ecgew,col='grey', lty='dashed')
legend("topright", legend =c(TeX(r'($\hat{S}_{CGE}(t,\hat{\tau})$)'),TeX(r'($\hat{S}(t,\hat{\tau})$)')),lty=c(2,1),col=c("grey","black"))                                                                                                                              
dev.off()


#Plots of estimated nonparametric S(t) for different tau



pdf("H:\\paper\\LoWilke2023\\code\\nonpara_surv.pdf")
plot(datQ[,1],ecgewm09, type='l', lty='dashed', xlab="life-time (in hours)", ylab=TeX(r'($S(t)$)'))
lines(datQ[,1],ecgew0,col='grey', type='l')
lines(datQ[,1],ecgew09,col='grey', lty='dashed')
legend("topright", legend =c(TeX(r'($\hat{S}_{CGE}(t,\tau=-0.9)$)'),TeX(r'($\hat{S}_{CGE}(t,\tau=0$))'),TeX(r'($\hat{S}_{CGE}(t,\tau=0.9)$)')),lty=c(3,1),col=c("black","grey","grey"))                                                                                                                              
dev.off()


#####################################
# Nonparametric bootstrap
#####################################
sims <- function(){
  x <- 1:n
 M<- sample(x, replace=TRUE) # length 2
  dat <- dat0[M,]

### START OPTIM and search for tau ###
# we need Qj and to estimate CGE.
  dat<-dat[order(dat$t),] # sort the data with t

  q <-cuminc(dat[,1],dat[,2],cencode=0) #estimate cumulative incidences
  tp <-timepoints(q,dat[,1]) # change the time grid to original data point
  eQ<-unname(t(tp[[1]])) # combine with t, delta, z
  
  for(i in 1:dim(eQ)[2]){
    eQ[is.na(eQ[,i]),i] <- -Inf  # Q has Na at the end of the column, so replace it to -inf
    eQ[is.infinite(eQ[,i]),i] <- max(eQ[,i])  # replace -inf to max of the column, i.e. Q(infty)
  }
  
  #vectors and matrices with unique time points and estimates
  ut<-as.data.frame(unique(dat[,1]))
  ut<-rbind(rep(0,1),ut) # add row of zeros as the first row
  eQ_1<-rbind(rep(0,1),eQ) # add row of zeros as the first row
  
  dt<-diff(ut[,1],lag=1)  # ti - t_{i-1} 
  ef<-diff(eQ_1,lag=1)/dt # first different of Qj = fj: add zero as first observation
  #ef[is.na(ef)] <- 0
  
  ut<-as.data.frame(unique(dat[,1])) # unique time points without leading 0
  
  #create matrices of zeros
  eQfull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
  effull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
  dtfull<-matrix(0, 1, nrow = length(dat[,1]))
 
  
  # create matrices of t, eQ and ef with row dimension equaling the number of observations.
  for(i in 1:dim(ut)[1]){
    I<-which(dat[,1]==ut[i,1])
    for(j in 1:k){
      eQfull[I,j]<-eQ[i,j]
      effull[I,j]<-ef[i,j]
    }
    dtfull[I,1]<-dt[i]
  }
  
datQ<-data.frame(dat,eQfull,effull,dtfull) # check the data of Qj

opttaub <- function(etau){
  # compute the estimated CGE
  
  datQu<-datQ
  
  datQu<-invisible(datQu %>% select(-2))
  
  datQu<-as.data.frame(unique(datQu)) # for unique t
  
  if (ecge == "clayton") {
    ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  if (ecge == "frank") {
    ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  if (ecge == "gumbel") {
    ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
  }
  
  ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
  ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
  
  #exclude observations with S_CGE=0 
  datQu<-datQu %>% filter(ecgewu > 0) 
  
  #inflate row length of ecgewu and 1u back to all observations
  #create matrices of 0
  ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
  
  
  for(i in 1:length(ecgewu)){
    I<-which(datQ[,1]==datQu[i,1])
    ecgew[I]<-ecgewu[i]
  }
  
  # estimate alpha using regression
  datQ<- data.frame(datQ,ecgew)
  y <- log(datQ$t) # tranform t to log(t)
  y[which(is.infinite(y))]<-NaN
  
  if (model == "expo") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    y<-y-lcge
    #datlm<-data.frame(y,z1) # run regression need a data frame
    fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
    eaw<-exp(-fit$coefficients[[1]])
    eSemiw <- exp(-datQ[,1]*eaw)
  }
  if (model == "weib") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- 1/fit$coefficients[[2]] # parameter transformation
    eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
    eSemiw <- exp(-(datQ[,1]*eaw)^ebw)  # construct Sj implie by the semimodel
  }
  if (model == "llog") {
    lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- -1/fit$coefficients[[2]] # parameter transformation
    eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
    eSemiw <- 1/(1+(datQ[,1]/eaw)^ebw)
  }
  eSemiw[is.na(eSemiw)] <- Inf  # eSemi has Na at the end of the column, so replace it to -inf
  eSemiw[is.infinite(eSemiw)] <- min(eSemiw)  # replace -inf to max of the column, i.e. Q(infty)
  I<-which(datQ[,1]<cen)
  CvM <- sum((ecgew[I]-eSemiw[I])^2) #  objective function is the mean squared sum error, restrict to below fixed censoring point
  return(CvM)
}


fb<-optim(startvalue, opttaub, method=c("Brent"), lower=c_l,upper=c_u)
#print(fb$par)
#f1<-optimize(opttaub, interval=c(c_l,c_u), tol=0.0000001, maximum=FALSE)
#print(f1$minimum)

# estimate parameter from regression using the esimated tau
datQu<-datQ
datQu<-invisible(datQu %>% select(-2))
datQu<-as.data.frame(unique(datQu)) # for unique t
if (ecge == "clayton") {
  ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
}
if (ecge == "frank") {
  ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
}
if (ecge == "gumbel") {
  ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
}
ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
#exclude observations with S_CGE=0 or S_CGE=1
datQu<-datQu %>% filter(ecgewu > 0 & ecgewu < 1) 
#inflate row length of ecgew0u and 1u back to all observations
#create matrices of 0
ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))

for(i in 1:length(ecgewu)){
  I0<-which(datQ[,1]==datQu[i,1])
  ecgew[I0]<-ecgewu[i]
}

# estimate alpha using regression
datQ<- data.frame(datQ,ecgew) # group z=0 and z =1 into one single data 
y <- log(datQ$t)
y[which(is.infinite(y))]<-NaN
if (model == "expo") {
  lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
  lcge[which(is.infinite(lcge))]<-NaN
  y<-y-lcge
  #datlm<-data.frame(y,z1) # run regression need a data frame
  fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
  eaw<-exp(-fit$coefficients[[1]])
  etau <- fb$par
}
if (model == "weib") {
  lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
  lcge[which(is.infinite(lcge))]<-NaN
  #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
  fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
  ebw <- 1/fit$coefficients[[2]] # parameter transformation
  eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
  etau <- fb$par
}
  if (model == "llog") {  
  lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
  lcge[which(is.infinite(lcge))]<-NaN
  #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
  fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
  ebw <- -1/fit$coefficients[[2]] # parameter transformation
  eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
  etau <- fb$par
  }
if (model != "expo") { 
  res <- list(etaub = etau, eawb = eaw, ebwb = ebw)
}
if (model == "expo") { 
  res <- list(etaub = etau, eawb = eaw)
}

return(res)
}


res2 <- vector("list", rep)
for(i in 1:rep) res2[[i]] <- try(sims(), TRUE)
res3<-res2[sapply(res2, function(x) !inherits(x, "try-error"))]

etaub<-rep(0,length(res3)) # create data frame for estimated beta
eawb<-rep(0,length(res3)) # create data frame for estimated beta
ebwb<-rep(0,length(res3)) # create data frame for estimated beta

if (model!="expo"){
for (i in 1:length(res3)){
  etaub[i]<-res3[[i]][[1]]
  eawb[i]<-res3[[i]][[2]]  
  ebwb[i]<-res3[[i]][[3]]
}
}
if (model=="expo"){
  for (i in 1:length(res3)){
    etaub[i]<-res3[[i]][[1]]
    eawb[i]<-res3[[i]][[2]]  
  }
} 

mtau = mean(etaub)
Vtau = mean((etaub-mean(etaub))^2)
maw = mean(eawb)
Vaw = mean((eawb-mean(eawb))^2)
if (model!="expo"){
mbw = mean(ebwb)
Vbw = mean((ebwb-mean(ebwb))^2)
}

############### report
n  # number of observations
rep  # bootstrap sample

f1$par #estimated tau
mtau # mean bootstrap tau
Vtau # variance for tau
quantile(etaub,0.025) # CI for etau
quantile(etaub,0.975) # CI for etau
2*f1$par-mtau # debiased estimate of tau

eaw # estimated alpha
maw # boostrap mean  alpha
Vaw # variance for alpha
quantile(eawb,0.025) # CI for alpha
quantile(eawb,0.975) # CI for alpha
2*eaw-maw # debiased estimate of alpha



if (model!="expo"){
  ebw #estimated sigma
}
if (model!="expo"){
  mbw # bootstrap mean  sigma
}
if (model!="expo"){
  Vbw # variance for sigma
}
if (model!="expo"){
  quantile(ebwb,0.025) # CI 
}
if (model!="expo"){
  quantile(ebwb,0.975) # CI for sigma
}
if (model!="expo"){
  2*ebw-mbw # debiased estimate of sigma
}







#####################################
# Semiparametric bootstrap
#####################################

# simulate marginals

simcc <- function(tau, k, n){ 
  if (tau==0){
    u<-matrix(runif(k*n),ncol=k)
    return(u)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    u <- rCopula(n, claytonCopula(theta, dim = k)) #  u1, u2 are the marginal from Clayton
    return(u)
  }
}


simfc <- function(tau, k, n){ 
  if (tau==0){
    u<-matrix(runif(k*n),ncol=k)
    return(u)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("frank"), tau)
    u <- rCopula(n, frankCopula(theta, dim = k)) #  u1, u2 are the marginal from frank
    return(u)
  }
}

simgc <- function(tau, k, n){ 
  if (tau==0){
    u<-matrix(runif(k*n),ncol=k)
    return(u)
  }
  if (tau!=0){
    theta <- iTau(archmCopula("gumbel"), tau)
    u <- rCopula(n, gumbelCopula(theta, dim = k)) #  u1, u2 are the marginal from gumbel
    return(u)
  }
}



sims <- function(){
  
  #create random sample
  
  if (ecge =="clayton"){
    u<-simcc(tau=f1$par, k=k, n=n) # simulate u from function simcc
  }
  
  if (ecge =="frank"){
    u<-simfc(tau=f1$par, k=k, n=n) # simulate u from function simfc
  }
  
  if (ecge =="gumbel"){
    u<-simgc(tau=f1$par, k=k, n=n) # simulate u from function simfc
  }
  
  #compute latent durations
  
  # Risk 1: parametric
  if (model == "expo") {
    tw<- invexpo(u[,1],eaw)  # simulate tw from exponential model/analytical inverted survival required
  }
  
  if (model == "weib") {
    tw<- invweib(u[,1],eaw,ebw)  # simulate tw from Weibull model/analytical inverted survival required
  }
  
  if (model == "llog") {
    tw<- invllogistic(u[,1],eaw,ebw)  # simulate tw from log-logistic model/analytical inverted survival required
  }
  
  #Risk 2: nonparametric
  tu<-matrix(NaN,ncol=1,nrow=n)
  for(i in 1:n){
  I<-which(ecgeu<=u[i,2])
  if (length(I)>0){
  tu[i]=datQ[min(I),1]
  }
  }
  
  tu[is.na(tu)] <- cen
  
  t <- pmin(tw,tu) # minimum of tw and tu
  delw = ifelse(tw<tu,1,2) # delw = 1 if risk w,  =2 if risk u 
  delw = ifelse(t>=630,0,delw)
  dat0 <- data.frame(t,delw)
  dat <- dat0
  summary(dat)
  
  ### START OPTIM and search for tau ###
  # we need Qj and to estimate CGE.
  dat<-dat[order(dat$t),] # sort the data with t
  
  q <-cuminc(dat[,1],dat[,2],cencode=0) #estimate cumulative incidences
  tp <-timepoints(q,dat[,1]) # change the time grid to original data point
  eQ<-unname(t(tp[[1]])) # combine with t, delta, z
  
  for(i in 1:dim(eQ)[2]){
    eQ[is.na(eQ[,i]),i] <- -Inf  # Q has Na at the end of the column, so replace it to -inf
    eQ[is.infinite(eQ[,i]),i] <- max(eQ[,i])  # replace -inf to max of the column, i.e. Q(infty)
  }
  
  #vectors and matrices with unique time points and estimates
  ut<-as.data.frame(unique(dat[,1]))
  ut<-rbind(rep(0,1),ut) # add row of zeros as the first row
  eQ_1<-rbind(rep(0,1),eQ) # add row of zeros as the first row
  
  dt<-diff(ut[,1],lag=1)  # ti - t_{i-1} 
  ef<-diff(eQ_1,lag=1)/dt # first different of Qj = fj: add zero as first observation
  #ef[is.na(ef)] <- 0
  
  ut<-as.data.frame(unique(dat[,1])) # unique time points without leading 0
  
  #create matrices of zeros
  eQfull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
  effull<-matrix(0, ncol = dim(eQ)[2] , nrow = length(dat[,1]))
  dtfull<-matrix(0, 1, nrow = length(dat[,1]))
  
  
  # create matrices of t, eQ and ef with row dimension equaling the number of observations.
  for(i in 1:dim(ut)[1]){
    I<-which(dat[,1]==ut[i,1])
    for(j in 1:k){
      eQfull[I,j]<-eQ[i,j]
      effull[I,j]<-ef[i,j]
    }
    dtfull[I,1]<-dt[i]
  }
  
  datQ<-data.frame(dat,eQfull,effull,dtfull) # check the data of Qj
  
  opttaub <- function(etau){
    # compute the estimated CGE
    
    datQu<-datQ
    
    datQu<-invisible(datQu %>% select(-2))
    
    datQu<-as.data.frame(unique(datQu)) # for unique t
    
    if (ecge == "clayton") {
      ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
    }
    if (ecge == "frank") {
      ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
    }
    if (ecge == "gumbel") {
      ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], etau) # estimate of cge
    }
    
    ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
    ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
    
    #exclude observations with S_CGE=0 
    datQu<-datQu %>% filter(ecgewu > 0)
    
    #inflate row length of ecgewu and 1u back to all observations
    #create matrices of 0
    ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
    
    
    for(i in 1:length(ecgewu)){
      I<-which(datQ[,1]==datQu[i,1])
      ecgew[I]<-ecgewu[i]
    }
    
    # estimate alpha using regression
    datQ<- data.frame(datQ,ecgew)
    y <- log(datQ$t) # tranform t to log(t)
    y[which(is.infinite(y))]<-NaN
    
    if (model == "expo") {
      lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
      lcge[which(is.infinite(lcge))]<-NaN
      y<-y-lcge
      #datlm<-data.frame(y,z1) # run regression need a data frame
      fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
      eaw<-exp(-fit$coefficients[[1]])
      eSemiw <- exp(-datQ[,1]*eaw)
    }
    if (model == "weib") {
      lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
      lcge[which(is.infinite(lcge))]<-NaN
      #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
      fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
      ebw <- 1/fit$coefficients[[2]] # parameter transformation
      eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
      eSemiw <- exp(-(datQ[,1]*eaw)^ebw)  # construct Sj implie by the semimodel
    }
    if (model == "llog") {
      lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
      lcge[which(is.infinite(lcge))]<-NaN
      #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
      fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
      ebw <- -1/fit$coefficients[[2]] # parameter transformation
      eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
      eSemiw <- 1/(1+(datQ[,1]/eaw)^ebw)
    }
    eSemiw[is.na(eSemiw)] <- Inf  # eSemi has Na at the end of the column, so replace it to -inf
    eSemiw[is.infinite(eSemiw)] <- min(eSemiw)  # replace -inf to max of the column, i.e. Q(infty)
    I<-which(datQ[,1]<cen)
    CvM <- sum((ecgew[I]-eSemiw[I])^2) #  objective function is the mean squared sum error, restrict to below fixed censoring point
    return(CvM)
  }
  
  fb<-optim(startvalue, opttaub, method=c("Brent"), lower=c_l,upper=c_u)
  #print(fb$par)
  #f1<-optimize(opttaub, interval=c(c_l,c_u), tol=0.0000001, maximum=FALSE)
  #print(f1$minimum)
  
  # estimate parameter from regression using the esimated tau
  datQu<-datQ
  datQu<-invisible(datQu %>% select(-2))
  datQu<-as.data.frame(unique(datQu)) # for unique t
  if (ecge == "clayton") {
    ecgewu = cgeclayton(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
  }
  if (ecge == "frank") {
    ecgewu = cgefrank(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
  }
  if (ecge == "gumbel") {
    ecgewu = cgegumbel(datQu[,2],datQu[,3],datQu[,4],datQu[,6], fb$par) # estimate of cge
  }
  ecgewu[is.na(ecgewu)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
  ecgewu[is.infinite(ecgewu)] <- min(ecgewu)  # replace -inf to max of the column, i.e. Q(infty)
  #exclude observations with S_CGE=0 or S_CGE=1
  datQu<-datQu %>% filter(ecgewu > 0 & ecgewu < 1) 
  #inflate row length of ecgew0u and 1u back to all observations
  #create matrices of 0
  ecgew<-matrix(0, ncol = 1 , nrow = length(dat[,1]))
  
  for(i in 1:length(ecgewu)){
    I0<-which(datQ[,1]==datQu[i,1])
    ecgew[I0]<-ecgewu[i]
  }
  
  # estimate alpha using regression
  datQ<- data.frame(datQ,ecgew) # group z=0 and z =1 into one single data 
  y <- log(datQ$t)
  y[which(is.infinite(y))]<-NaN
  if (model == "expo") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    y<-y-lcge
    #datlm<-data.frame(y,z1) # run regression need a data frame
    fit<-lm(formula =y ~ 1 ) # regress log(t)-log(-log(cge)) on a constant (=sample average)
    eaw<-exp(-fit$coefficients[[1]])
  }
  if (model == "weib") {
    lcge<- log(-log(datQ$ecgew)) # transform ecge to log(-log)
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- 1/fit$coefficients[[2]] # parameter transformation
    eaw<-exp(-fit$coefficients[[1]])  # parameter transformation
  }
  if (model == "llog") {  
    lcge<- log(datQ$ecgew/(1-datQ$ecgew)) # transform ecge to log(s/(1-s))
    lcge[which(is.infinite(lcge))]<-NaN
    #datlm<-data.frame(y,lcge,z1) # run regression need a dataframe
    fit<-lm(formula =y ~ lcge ) # regress log(t) on log(-log(cge)), z, ann constant
    ebw <- -1/fit$coefficients[[2]] # parameter transformation
    eaw<- 1/exp(-fit$coefficients[[1]])  # parameter transformation
  }
  etau <- fb$par
  eCvM <- fb$value
  if (model != "expo") { 
    res <- list(eCvMb=eCvM, etaub = etau, eawb = eaw, ebwb = ebw)
  }
  if (model == "expo") { 
    res <- list(eCvMb=eCvM, etaub = etau, eawb = eaw)
  }
  
  return(res)
}


res2 <- vector("list", rep)
for(i in 1:rep) res2[[i]] <- try(sims(), TRUE)
res3<-res2[sapply(res2, function(x) !inherits(x, "try-error"))]

eCvMb<-rep(0,length(res3))  # create data frame for estimates
etaub<-rep(0,length(res3))
eawb<-rep(0,length(res3)) 
ebwb<-rep(0,length(res3)) 

if (model!="expo"){
  for (i in 1:length(res3)){
    eCvMb[i]<-res3[[i]][[1]]
    etaub[i]<-res3[[i]][[2]]
    eawb[i]<-res3[[i]][[3]]  
    ebwb[i]<-res3[[i]][[4]]
  }
}
if (model=="expo"){
  for (i in 1:length(res3)){
    eCvMb[i]<-res3[[i]][[1]]
    etaub[i]<-res3[[i]][[2]]
    eawb[i]<-res3[[i]][[3]]  
  }
} 

mCvM = mean(eCvMb)
VCvM = mean((eCvMb-mean(eCvMb))^2)
mtau = mean(etaub)
Vtau = mean((etaub-mean(etaub))^2)
maw = mean(eawb)
Vaw = mean((eawb-mean(eawb))^2)
if (model!="expo"){
  mbw = mean(ebwb)
  Vbw = mean((ebwb-mean(ebwb))^2)
}

############### report
n  # number of observations
rep  # number of bootstrap samples

f1$value #CvM
mCvM # average CvM
VCvM # variance CvM
quantile(eCvMb,0.90) # CI for CvM
quantile(eCvMb,0.95) # CI for CvM
I <- which(f1$value>eCvMb)
1-(length(I)/rep)  # p-value bootstrap test

mtau # bootstrap mean tau
Vtau # variance for tau
quantile(etaub,0.025) # CI for etau
quantile(etaub,0.975) # CI for etau

maw # bootstrap mean alpha
Vaw # variance for alpha
quantile(eawb,0.025) # CI for alpha
quantile(eawb,0.975) # CI for alpha

if (model!="expo"){
  ebw #estimated sigma
}
if (model!="expo"){
  mbw # bootstrap mean  sigma
}
if (model!="expo"){
  Vbw # variance for sigma
}
if (model!="expo"){
  quantile(ebwb,0.025) # CI 
}
if (model!="expo"){
  quantile(ebwb,0.975) # CI for sigma
}
if (model!="expo"){
  2*ebw-mbw # debiased estimate of sigma
}



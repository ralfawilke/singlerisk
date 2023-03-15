# This is sample code for the simulation of data and estimation as in the paper
# "A single risk approach to the semiparametric competing
# risks model with parametric Archimedean risk dependence"
# by Simon M.S. Lo and Ralf A. Wilke

rm(list = ls())

library(PairedData)
library(copula)
library(survival)
library(pastecs)
library(cmprsk)
library(timereg)
library(MALDIquant)
library(plyr)
library(dplyr)
library(latex2exp)

# define functions in relation to the copula generator

invpsiclayton <- function(s, tau){  # inverse copula generator of clayton
  if (tau==0){
    u <- exp(-s)
  }  
  if (tau!=0){
    theta <- iTau(archmCopula("clayton"), tau)
    u <- (theta*s+1)^(-1/theta)
    u[is.na(u)] <- 1e-16
  }
  return(u)
}

dpsiclayton <- function(s, tau){  # derivative of copula generator of clayton
  s[s < 0] <- 1e-16
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


# we define the function for log-logistic distribution with covariate z

llogistic <- function(t,z, a, b , beta){  # survival function
  u<-(1+(exp(z*beta)*t/a)^(b))^(-1)
}

## b = 1/sigma, a = 1/lambda

dllogistic <- function(t,z, a, b, beta){ # hazard function
  u <- ((b/a)*(exp(z*beta)*t/a)^(b-1))/(1+(exp(z*beta)*t/a)^b)
}

invllogistic <- function(u,z,a, b, beta){
  t = a*exp(-z*beta)*(u^(-1)-1)^(1/b)
}


# we define the function for weibull distribution with covariate z

weib <- function(t,z, a, b , beta){  # survival function
  u<-exp(-(a*t)^b*exp(z*beta))
}

dweib <- function(t,z, a, b, beta){ # hazard function
  u <- a^b*b*exp(z*beta)*t^(b-1)*exp(-(a*t)^b*exp(z*beta))
}

invweib <- function(u,z,a, b, beta){
  t = (-log(u)/a^b/exp(z*beta))^(1/b)
}

# we define the function for expo distribution with covariate z

expo <- function(t,z, a, beta){  # survival function
  u<-exp(-a*t*exp(z*beta))
}

dexpo <- function(t,z, a,beta){ # hazard function
  u <- a*exp(z*beta)*exp(-a*t*exp(z*beta))
}

invexpo <- function(u,z,a,beta){
  t = -log(u)/a/exp(z*beta)
}

###################################
# SETUP
###################################

#set.seed(11111)

n<-2000 # observations
k <- 2 # dimensions
tau <- 0.3 # ktau
beta1w <- 1 # coeff. of z1 on tw
beta1u <- 1 # coeff. of z1 on tu
pz <- 0.3 # prob of z1 = 1
aw <- 1  # scale of log-logistic baseline survival (median) - working duration till new job
bw <- 1.5  # shape of log-logistic baseline survival (unimodel if b>1, dispersion smaller for greater b)
au <- 1  # scale of log-logistic baseline survival (median) - working duration till unemp
bu <- 1.5  # shape of log-logistic baseline survival (unimodel if b>1, dispersion smaller for greater b)
z11 <-1  # value of z1
z10 <-0  # value of z1

tqlimmin <- 0.01 # set lower threshold for duration for estimation and plotting
tqlimmax <- 0.90 # set upper threshold for duration for estimation and plotting, max is quantile of tqlim
tqlim <- tqlimmax  # when plotting the graph, max is quantile of tqlim

#discrete data? =1 generates discrete duration data
d=0
#ceiling level 100= in 1/hundreds
cl=100

# model choice: "expo" ","weib" "llog" 

#model = "expo"
model = "weib"
#model = "llog"


# DGP: copula choice: "clayton" ","frank" 

gcge = "clayton"
#gcge = "frank"


# Estimation: copula choice: "clayton" ","frank" 
# 2 copula choices for specification test

ecge1 = "clayton"
#ecge1 = "frank"

#ecge2 = "clayton"
ecge2 = "frank"

#Set range of tau for cge2 for OPTIONAL plots:
taugd <-c(seq(-0.7,0.7,0.05))

#Set range of tau for cge for numerical minimisation of the variance criterion in theta:
# for ecge1
c1_l=-0.7
c1_u=0.7
# for ecge2
c2_l=-0.7
c2_u=0.7

###################################

# the following steps are to find a time grid for evaluation in simulation

# we first simulate the data for one sample and find the qunatile

if (gcge =="clayton"){
  u<-simcc(tau=tau, k=k, n=n*100) # simulate u from function simcc
}

if (gcge =="frank"){
  u<-simfc(tau=tau, k=k, n=n*100) # simulate u from function simfc
}

corKendall(u)

z1<-rbinom(n*100,1,pz)  # simulate z1 ~ Bern(n,pz)
z1<-ifelse(z1==1,z11,z10)

if (model == "expo") {
tw<- invexpo(u[,1],z1,aw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
tu<-invexpo(u[,2],z1,au,beta1u)
}

if (model == "weib") {
  tw<- invweib(u[,1],z1,aw,bw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
  tu<-invweib(u[,2],z1,au,bu,beta1u)
}

if (model == "llog") {
  tw<- invllogistic(u[,1],z1,aw,bw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
  tu<-invllogistic(u[,2],z1,au,bu,beta1u)
}

t <- pmin(tw,tu) # minimum of tw and tu
delw = ifelse(tw<tu,1,2) # delw = 1 if risk w,  =2 if risk u 
mean(delw)
summary(t)

#discrete time
if (d == 1) {
  t<-ceiling(cl*t)/cl
}

#tmax <- quantile(t,c(tqlim))
# #grid <- seq(from = 0, to = tmax, length.out = n)

dat <- data.frame(t,delw,z1,tw,tu) # data frame containing all relevant data
z <-c(z11,z10)

### START OPTIM and search for tau ###

# STEP 3: Compute the CGE and the BETA in terms of theta

# we need Qj and to estimate CGE.

dat<-dat[order(dat$t),] # sort the data with t
dat0<-dat[which(dat[,3]==0),] # data with z=0
dat1<-dat[which(dat[,3]==1),] # data with z=1

#grid&limits for plot & estimation

tmin <- quantile(t,c(tqlimmin))
tmax0 = min(max(dat0$t),max(dat1$t))
tmax <- quantile(t[which(t<tmax0)],c(tqlimmax))
grid <- seq(from = 0, to = tmax, length.out = 300) #length.out = n)
tmin
tmax
tmax0

###############################################
###############################################
###############################################
###############################################

# StEP 1: simulate the marginals from copula

if (gcge== "clayton"){
  u<-simcc(tau=tau, k=k, n=n) # simulate u from function simcc
}

if (gcge== "frank"){
  u<-simfc(tau=tau, k=k, n=n) # simulate u from function simfc
}


corKendall(u)


# STEP 2: simulate the marginal durations and covariates

z1<-rbinom(n,1,pz)  # simulate z1 ~ Bern(n,pz) 
z1<-ifelse(z1==1,z11,z10)
#mean(z1) #check z1

n0<-length(which(z1==0))
n1<-length(which(z1==1))

if (model == "expo") {
  tw<- invexpo(u[,1],z1,aw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
  tu<-invexpo(u[,2],z1,au,beta1u)
}

if (model == "weib") {
  tw<- invweib(u[,1],z1,aw,bw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
  tu<-invweib(u[,2],z1,au,bu,beta1u)
}

if (model == "llog") {
  tw<- invllogistic(u[,1],z1,aw,bw,beta1w)  # simulate tw (working duration) from log-logistic cox model/analytical inverses required
  tu<-invllogistic(u[,2],z1,au,bu,beta1u)
}

delw = ifelse(tw<tu,1,2) # delw = 1 if risk w,  =2 if risk u 
t <- pmin(tw,tu) # minimum of tw and tu



#discrete time
if (d == 1) {
  t<-ceiling(cl*t)/cl
}

dat <- data.frame(t,delw,z1,tw,tu) # data frame containing all relevant data
dat<-dat[order(dat$t),]

summary(dat)  # summary of data
summary(dat[which(dat[,3]==0),]) # summary of data with z=0
summary(dat[which(dat[,3]==1),]) # summary of data with z=1
table(delw,z1)
z <-c(z11,z10)


# STEP 3: Compute the CGE and the BETA in terms of theta
# we need Qj and to estimate CGE.

dat<-dat[order(dat$t),] # sort the data with t
dat0<-dat[which(dat[,3]==0),] # data with z=0
dat1<-dat[which(dat[,3]==1),] # data with z=1

q0 <-cuminc(dat0[,1],dat0[,2]) # time grid is not the same as original data  point
tp0 <-timepoints(q0,dat[,1]) # change the time grid to original data point
eQ0<-unname(t(tp0[[1]])) # combine with t, delta, z

q1 <-cuminc(dat1[,1],dat1[,2]) # time grid is not the same as original data  point
tp1 <-timepoints(q1,dat[,1]) # change the time grid to original data point
eQ1<-unname(t(tp1[[1]])) # combine with t, delta, z

for(i in 1:dim(eQ0)[2]){
  eQ0[is.na(eQ0[,i]),i] <- -Inf  # Q has Na at the end of the column, so replace it to -inf
  eQ0[is.infinite(eQ0[,i]),i] <- max(eQ0[,i])  # replace -inf to max of the column, i.e. Q(infty)
  eQ1[is.na(eQ1[,i]),i] <- -Inf  # Q has Na at the end of the column, so replace it to -inf
  eQ1[is.infinite(eQ1[,i]),i] <- max(eQ1[,i])  # replace -inf to max of the column, i.e. Q(infty)
}

#vectors and matrices with unique time points and estimates
ut<-as.data.frame(unique(dat[,1]))
ut<-rbind(rep(0,1),ut) # add row of zeros as the first row
dt<-diff(ut[,1],lag=1)  # ti - t_{i-1} 

eQ0_1<-rbind(rep(0,1),eQ0) # add row of zeros as the first row
ef0<-diff(eQ0_1,lag=1)/dt # first different of Qj = fj: add zero as first observation

eQ1_1<-rbind(rep(0,1),eQ1) # add row of zeros as the first row
ef1<-diff(eQ1_1,lag=1)/dt # first different of Qj = fj: add zero as first observation

ut<-as.data.frame(unique(dat[,1])) # unique time points without leading 0

#create matrices of zeros
eQ0full<-matrix(0, ncol = dim(eQ0)[2] , nrow = length(dat[,1]))
eQ1full<-matrix(0, ncol = dim(eQ0)[2], nrow = length(dat[,1]))
ef0full<-matrix(0, ncol = dim(eQ0)[2] , nrow = length(dat[,1]))
ef1full<-matrix(0, ncol = dim(eQ0)[2], nrow = length(dat[,1]))
dtfull<-matrix(0, 1, nrow = length(dat[,1]))

# create matrices of t, eQ and ef with row dimension equaling the number of observations.
for(i in 1:dim(ut)[1]){
  I<-which(dat[,1]==ut[i,1])
  for(j in 1:k){
    eQ0full[I,j]<-eQ0[i,j]
    ef0full[I,j]<-ef0[i,j]
    eQ1full[I,j]<-eQ1[i,j]
    ef1full[I,j]<-ef1[i,j]
  }
  dtfull[I,1]<-dt[i]
}

datQ0<-data.frame(dat,eQ0full,ef0full,dtfull) # check the data of Qj
datQ1<-data.frame(dat,eQ1full,ef1full,dtfull) # check the data of Qj


### START OPTIM and search for tau ###

opttau1 <- function(etau){

# compute the estimated CGE at unique values of observed durations

  datQ0u<-datQ0
  datQ1u<-datQ1
  
  datQ0u<-invisible(datQ0u %>% select(-2, -3, -4, -5))
  datQ1u<-invisible(datQ1u %>% select(-2, -3, -4, -5))
  
  datQ0u<-as.data.frame(unique(datQ0u)) # for unique t
  datQ1u<-as.data.frame(unique(datQ1u)) # for unique t

if (ecge1 == "clayton") {
  ecgew0u = cgeclayton(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
  ecgew1u = cgeclayton(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
}

if (ecge1 == "frank") {
  ecgew0u = cgefrank(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
  ecgew1u = cgefrank(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
}

# address numerical and boundary issues

ecgew0u[is.na(ecgew0u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew0u[is.infinite(ecgew0u)] <- min(ecgew0u)  # replace -inf to max of the column, i.e. Q(infty)
ecgew1u[is.na(ecgew1u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew1u[is.infinite(ecgew1u)] <- min(ecgew1u)  # replace -inf to max of the column, i.e. Q(infty)

#exclude observations with S_CGE=0
datQ0u<-datQ0u %>% filter(ecgew0u > 0) 
datQ1u<-datQ1u %>% filter(ecgew1u > 0)

I<-which(ecgew0u > 0)
ecgew0u<-ecgew0u[I] 
I<-which(ecgew1u > 0)
ecgew1u<-ecgew1u[I]

#inflate row length of ecgew0u and 1u back to all observations
#create matrices of NaN

ecgew0<-matrix(NaN, ncol = 1 , nrow = length(datQ0[,1]))
ecgew1<-matrix(NaN, ncol = 1, nrow = length(datQ1[,1]))

#cut boundary of t  
datQ0<-datQ0 %>% filter(t > tmin & t < tmax) 
datQ1<-datQ1 %>% filter(t > tmin & t < tmax)

for(i in 1:length(datQ0[,1])){
  I<-which(datQ0[,1]==datQ0u[i,1]) #time points in dat, datQ0 and datQ1 must be the same
  ecgew0[I]<-ecgew0u[i]
  ecgew1[I]<-ecgew1u[i]
}


ebeta1w <- log(log(ecgew1)/log(ecgew0)) # when t is small, ecge is 1, so 0/0 will have NaN

mebeta1w <- mean(ebeta1w[is.nan(ebeta1w)==FALSE & is.finite(ebeta1w)])  # take the sample mean of beta
vebeta1w <- var(ebeta1w[is.nan(ebeta1w)==FALSE & is.finite(ebeta1w)])

mebeta1w
beta1w
vebeta1w

return(vebeta1w)

}

opttau2 <- function(etau){
  # compute the estimated CGE at unique values of observed durations
  
  datQ0u<-datQ0
  datQ1u<-datQ1
  
  datQ0u<-invisible(datQ0u %>% select(-2, -3, -4, -5))
  datQ1u<-invisible(datQ1u %>% select(-2, -3, -4, -5))
  
  datQ0u<-as.data.frame(unique(datQ0u)) # for unique t
  datQ1u<-as.data.frame(unique(datQ1u)) # for unique t

  
  if (ecge2 == "clayton") {
    ecgew0u = cgeclayton(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
    ecgew1u = cgeclayton(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
  }
  
  if (ecge2 == "frank") {
    ecgew0u = cgefrank(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
    ecgew1u = cgefrank(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
  }
 
  # address numerical and boundary issues

  ecgew0u[is.na(ecgew0u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
  ecgew0u[is.infinite(ecgew0u)] <- min(ecgew0u)  # replace -inf to max of the column, i.e. Q(infty)
  ecgew1u[is.na(ecgew1u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
  ecgew1u[is.infinite(ecgew1u)] <- min(ecgew1u)  # replace -inf to max of the column, i.e. Q(infty)
  
  #exclude observations with S_CGE=0
  datQ0u<-datQ0u %>% filter(ecgew0u > 0) 
  datQ1u<-datQ1u %>% filter(ecgew1u > 0)
  
  I<-which(ecgew0u > 0)
  ecgew0u<-ecgew0u[I] 
  I<-which(ecgew1u > 0)
  ecgew1u<-ecgew1u[I]
  
  #inflate row length of ecgew0u and 1u back to all observations
  #create matrices of zeros
  
  ecgew0<-matrix(NaN, ncol = 1 , nrow = length(datQ0[,1]))
  ecgew1<-matrix(NaN, ncol = 1, nrow = length(datQ1[,1]))
  
  #cut boundary of t  
  datQ0<-datQ0 %>% filter(t > tmin & t < tmax) 
  datQ1<-datQ1 %>% filter(t > tmin & t < tmax)

  
  for(i in 1:length(datQ0[,1])){
    I<-which(datQ0[,1]==datQ0u[i,1]) #time points in dat, datQ0 and datQ1 must be the same
    ecgew0[I]<-ecgew0u[i]
    ecgew1[I]<-ecgew1u[i]
  }
  
  
  ebeta1w <- log(log(ecgew1)/log(ecgew0)) # when t is small, ecge is 1, so 0/0 will have NaN
  
  mebeta1w <- mean(ebeta1w[is.nan(ebeta1w)==FALSE & is.finite(ebeta1w)])  # take the sample mean of beta
  vebeta1w <- var(ebeta1w[is.nan(ebeta1w)==FALSE & is.finite(ebeta1w)])
  
  
  mebeta1w
  beta1w
  vebeta1w
  
  return(vebeta1w)
  
}

#################
#OPTION: plot criterion function in tau for second assumed copula (ecge2)
# Can be helpful for choosing initial values or to check shape of the objective function.

f_2<- rep(NA,length(taugd))
for(i in 1:length(taugd)){
  f_2[i] <- opttau2(taugd[i])
}

#plot objective function for 2nd copula
#pdf("H:\\PATH\\variance_criterion.pdf")
#plot(taugd, f_2, type='l',axes=FALSE, xlab=TeX(r'($\tau$)'), ylab="Criterion")
#axis(1, taugd)
#axis(2)
#dev.off()
################

#Estimate the model for the two assumed copulas

f1<-optimize(opttau1, interval=c(c1_l,c1_u), tol=0.0000001, maximum=FALSE)
f2<-optimize(opttau2, interval=c(c2_l,c2_u), tol=0.0000001, maximum=FALSE)

# Estimated tau and value of the aobjective function for the two assumed copulas.
etau1<-f1[[1]]
obj1<-f1[[2]]

etau2<-f2[[1]]
obj2<-f2[[2]]

################################
# Grambsch (1994) copula specification test  
################################

datQ0u<-datQ0
datQ1u<-datQ1

datQ0u<-invisible(datQ0u %>% select(-2, -3, -4, -5))
datQ1u<-invisible(datQ1u %>% select(-2, -3, -4, -5))

datQ0u<-as.data.frame(unique(datQ0u)) # for unique t
datQ1u<-as.data.frame(unique(datQ1u)) # for unique t


if (ecge1 == "clayton") {
  ecgew0u = cgeclayton(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau1) # estimate of cge
  ecgew1u = cgeclayton(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau1)
}

if (ecge1 == "frank") {
  ecgew0u = cgefrank(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau1) # estimate of cge
  ecgew1u = cgefrank(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau1)
}

 # address numerical and boundary issues

ecgew0u[is.na(ecgew0u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew0u[is.infinite(ecgew0u)] <- min(ecgew0u)  # replace -inf to max of the column, i.e. Q(infty)
ecgew1u[is.na(ecgew1u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew1u[is.infinite(ecgew1u)] <- min(ecgew1u)  # replace -inf to max of the column, i.e. Q(infty)

#exclude observations with S_CGE=0
datQ0u<-datQ0u %>% filter(ecgew0u > 0) 
datQ1u<-datQ1u %>% filter(ecgew1u > 0)

I<-which(ecgew0u > 0)
ecgew0u<-ecgew0u[I] 
I<-which(ecgew1u > 0)
ecgew1u<-ecgew1u[I]

#inflate row length of ecgew0u and 1u back to all observations
#create matrices of NaN

ecgew0<-matrix(NaN, ncol = 1 , nrow = length(datQ0[,1]))
ecgew1<-matrix(NaN, ncol = 1, nrow = length(datQ1[,1]))

#cut boundary of t  
#datQ0<-datQ0 %>% filter(t >= tmin & t <= tmax) 
#datQ1<-datQ1 %>% filter(t >= tmin & t <= tmax)

for(i in 1:length(datQ0[,1])){
  I<-which(datQ0[,1]==datQ0u[i,1]) #time points in dat, datQ0 and datQ1 must be the same
  ecgew0[I]<-ecgew0u[i]
  ecgew1[I]<-ecgew1u[i]
}


ebeta1w1 <- log(log(ecgew1)/log(ecgew0)) # when t is small, ecge is 1, so 0/0 will have NaN
ebeta1w1[is.infinite(ebeta1w1)]<- NA

mebeta1w1 <- mean(ebeta1w1[is.nan(ebeta1w1)==FALSE & is.finite(ebeta1w1)])  # take the sample mean of beta
vebeta1w1 <- var(ebeta1w1[is.nan(ebeta1w1)==FALSE & is.finite(ebeta1w1)])


##########################
  
datQ0u<-datQ0
datQ1u<-datQ1

datQ0u<-invisible(datQ0u %>% select(-2, -3, -4, -5))
datQ1u<-invisible(datQ1u %>% select(-2, -3, -4, -5))

datQ0u<-as.data.frame(unique(datQ0u)) # for unique t
datQ1u<-as.data.frame(unique(datQ1u)) # for unique t

  
if (ecge2 == "clayton") {
    ecgew0u = cgeclayton(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau2) # estimate of cge
    ecgew1u = cgeclayton(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau2)
  }

if (ecge2 == "frank") {
  ecgew0u = cgefrank(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau2) # estimate of cge
  ecgew1u = cgefrank(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau2)
}

# address numerical and boundary issues
ecgew0u[is.na(ecgew0u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew0u[is.infinite(ecgew0u)] <- min(ecgew0u)  # replace -inf to max of the column, i.e. Q(infty)
ecgew1u[is.na(ecgew1u)] <- Inf  # ecgew has Na at the end of the column, so replace it to -inf
ecgew1u[is.infinite(ecgew1u)] <- min(ecgew1u)  # replace -inf to max of the column, i.e. Q(infty)

#exclude observations with S_CGE=0
datQ0u<-datQ0u %>% filter(ecgew0u > 0) 
datQ1u<-datQ1u %>% filter(ecgew1u > 0)

I<-which(ecgew0u > 0)
ecgew0u<-ecgew0u[I] 
I<-which(ecgew1u > 0)
ecgew1u<-ecgew1u[I]

#inflate row length of ecgew0u and 1u back to all observations
#create matrices of NaN

ecgew0<-matrix(NaN, ncol = 1 , nrow = length(datQ0[,1]))
ecgew1<-matrix(NaN, ncol = 1, nrow = length(datQ1[,1]))

#cut boundary of t  
datQ0<-datQ0 %>% filter(t >= tmin & t <= tmax) 
datQ1<-datQ1 %>% filter(t >= tmin & t <= tmax)

for(i in 1:length(datQ0[,1])){
  I<-which(datQ0[,1]==datQ0u[i,1]) #time points in dat, datQ0 and datQ1 must be the same
  ecgew0[I]<-ecgew0u[i]
  ecgew1[I]<-ecgew1u[i]
}


ebeta1w2 <- log(log(ecgew1)/log(ecgew0)) # when t is small, ecge is 1, so 0/0 will have NaN
ebeta1w2[is.infinite(ebeta1w2)]<- NA

mebeta1w2 <- mean(ebeta1w2[is.nan(ebeta1w2)==FALSE & is.finite(ebeta1w2)])  # take the sample mean of beta
vebeta1w2 <- var(ebeta1w2[is.nan(ebeta1w2)==FALSE & is.finite(ebeta1w2)])

#######################
beta1w
mebeta1w1
vebeta1w1

beta1w
mebeta1w2
vebeta1w2

gcge
ecge1
tau
etau1
obj1

gcge
ecge2
tau
etau2
obj2


I<- !is.na(ebeta1w1) & !is.na(ebeta1w2)
v1<- c(ebeta1w1[which(I==TRUE)])
v2<- c(ebeta1w2[which(I==TRUE)])
var(v1)
var(v2)
var(v2)/var(v1)
EBETA<-data.frame(v1,v2)
var.test(v2, v1, alternative = "greater")
Ftest<-var.test(v2, v1, alternative = "greater")

Fstat <-Ftest$statistic
Fpvalue <-Ftest$p.value
Fdfa <- Ftest$parameter[1]
Fdfb <- Ftest$parameter[2]

p<-with(EBETA, paired(v2,v1))
Var.test(p)
PMtest <- Var.test(p)
PMtest$statistic
PMtest$p.value
PMtest$parameter

Var.test(EBETA$v1,EBETA$v2,paired=TRUE)
p<-with(EBETA,paired(v1,v2))
Var.test(p)

# Results of the test.

Gtest<-grambsch.Var.test(v2,v1, alternative = c("greater"))
Gtest$statistic
Gtest$p.value
Gtest$parameter

##########################################

# Option: CvM criterion
###############

# plot cvm objective function for 2nd copula on tau grid

opttau_cvm <- function(etau){
  # compute the estimated CGE for "ecge2"
  
  
  datQ0u<-datQ0
  datQ1u<-datQ1
  
  datQ0u<-invisible(datQ0u %>% select(-2, -3, -4, -5))
  datQ1u<-invisible(datQ1u %>% select(-2, -3, -4, -5))
  
  #datQ0u$delw <- NULL
  #datQ0u$z1 <- NULL
  #datQ1u$delw <- NULL
  #datQ1u$z1 <- NULL
  
  datQ0u<-as.data.frame(unique(datQ0u)) # for unique t
  datQ1u<-as.data.frame(unique(datQ1u)) # for unique t
  
  
  if (ecge2 == "clayton") {
    ecgew0u = cgeclayton(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
    ecgew1u = cgeclayton(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
  }
  
  if (ecge2 == "frank") {
    ecgew0u = cgefrank(datQ0u[,2],datQ0u[,3],datQ0u[,4],datQ0u[,6], etau) # estimate of cge
    ecgew1u = cgefrank(datQ1u[,2],datQ1u[,3],datQ1u[,4],datQ1u[,6], etau)
  }
  
  #inflate row length of ecgew0u and 1u back to all observations
  #create matrices of NaN
  
  ecgew0u[is.na(ecgew0u)] <- 0  # ecgew has Na at the end of the column, so replace it to -inf
  ecgew1u[is.na(ecgew1u)] <- 0  # ecgew has Na at the end of the column, so replace it to -inf

  #exclude observations with S_CGE=0
  datQ0u<-datQ0u %>% filter(ecgew0u > 0) 
  datQ1u<-datQ1u %>% filter(ecgew1u > 0)
  
  I<-which(ecgew0u > 0)
  ecgew0u<-ecgew0u[I] 
  I<-which(ecgew1u > 0)
  ecgew1u<-ecgew1u[I]
  
  
  #cut boundary of t  
  datQ0<-datQ0 %>% filter(t > tmin & t < tmax) 
  datQ1<-datQ1 %>% filter(t > tmin & t < tmax)
  
  ecgew0<-matrix(NaN, ncol = 1 , nrow = length(datQ0[,1]))
  ecgew1<-matrix(NaN, ncol = 1, nrow = length(datQ1[,1]))
  
  for(i in 1:length(datQ0[,1])){
    I<-which(datQ0[,1]==datQ0u[i,1]) #time points in dat, datQ0 and datQ1 must be the same
    ecgew0[I]<-ecgew0u[i]
    ecgew1[I]<-ecgew1u[i]
  }
  
  ebeta1w <- log(log(ecgew1)/log(ecgew0)) # when t is small, ecge is 1, so 0/0 will have NaN
 
  mebeta1w <- mean(ebeta1w[is.nan(ebeta1w)==FALSE & is.finite(ebeta1w)])  # take the sample mean of beta
  
  # Step 4 : compute L0(t) using theta
  
  eL0t0 <- -log(ecgew0)  # for z =0, eL0t0 is the same as -ln(ecgew0)
  eL0t1 <- -log(ecgew1)/exp(z[1]*mebeta1w)  # for z =0, eL0t0 is the same as -ln(ecgew0)
  
  h0<-1*!is.na(eL0t0)
  h1<-1*!is.na(eL0t1)
  
  eL0t0[is.na(eL0t0)] <- 0
  eL0t1[is.na(eL0t1)] <- 0
  
  #weighted average of cum. baseline hazards for z=0 and z=1
  eL0<- (eL0t0*h0*n0/n+eL0t1*h1*n1/n)/(h0*n0/n+h1*n1/n)
  
  # Step 5 : compute eSemi using theta
  
  eSemi1w <- exp(-eL0*exp(z[1]*mebeta1w))
  eSemi0w <- exp(-eL0)
  
  #recode CGE to missing when no implied survival
  I<-which(!is.na(eL0))
  eSemi0w<-eSemi0w[I]
  eSemi1w<-eSemi1w[I]
  ecgew0<-ecgew0[I]
  ecgew1<-ecgew1[I]
  
  #Plots of estimated S(t|z) for different value of z.
  #plot survival for z=0
  #pdf("H:\\PATH\\Semipara_surv_z0.pdf")
  #plot(datQ0[,1],eSemi0w, type='l', xlab="duration", ylab=TeX(r'($S(t|z)$)'))
  #lines(datQ0[,1],ecgew0,col='grey', lty='dashed')
  #legend("topright", legend =c(TeX(r'($\hat{S}_{CGE}(t|z=0,\hat{\tau})$)'),TeX(r'($\hat{S}(t|z=0,\hat{\tau})$)')),lty=c(1,2),col=c("grey","black"))                                                                                                                              
  #dev.off()
  
  #plot survival for z=1
  #pdf("H:\\PATH\\Semipara_surv_z1.pdf")
  #plot(datQ1[,1],eSemi1w, type='l', xlab="duration", ylab=TeX(r'($S(t|z)$)'))
  #lines(datQ1[,1],ecgew1,col='grey', lty='dashed')
  #legend("topright", legend =c(TeX(r'($\hat{S}_{CGE}(t|z=1,\hat{\tau})$)'),TeX(r'($\hat{S}(t|z=1,\hat{\tau})$)')),lty=c(1,2),col=c("grey","black"))                                                                                                                              
  #dev.off()
  
  # Step 6 : compute cvm
  
  obj<-sum((ecgew0-eSemi0w)^2)+sum((ecgew1-eSemi1w)^2)
  return(obj)
  
}

f_cvm<- rep(NA,length(taugd))
for(i in 1:length(taugd)){
  f_cvm[i] <- opttau_cvm(taugd[i])
}

#plot objective function for 2nd copula
#pdf("H:\\PATH\\cvm_criterion.pdf")
#plot(taugd, f_cvm, type='l',axes=FALSE, xlab=TeX(r'($\tau$)'), ylab="Criterion")
#axis(1, taugd)
#axis(2)
#dev.off()


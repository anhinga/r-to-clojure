trpol2 <- function(n,x) {
  mu <<- 10.0
  pu <<- 0.0
  pol <<- 1:100
  tp1 <<- 2.0
  tm1 <<- 1/2.0
  for (i in 1:n) {
    for (j in 1:100) {
      mu <<- (mu + tp1) * tm1
      pol[j] <<- mu
    }
    s <<- 0.0;
    for (j in 1:100) {
      s <<- x*s + pol[j];
    }
    pu <- s+pu;
  }
  print(pu)
  return(pu)
}

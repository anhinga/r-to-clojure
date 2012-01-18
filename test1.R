test1 <- function(x, exp) {
  res <<- 1.0
  for (i in 1:exp) {
    res <<- res * x
  }
  return(res)
}

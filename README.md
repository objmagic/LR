# LR
explore different techniques to generate LR(k) parsing code

# Plans

* Normal approach

  * very naive LR(1) parsing algorithm. use hardcoded lr(1) parsing code to interpret array-based table  

* Automata simulated by GADT 

  * Hardcoded GADT  

  * Hardcoded optimized GADT  



  * token information --> optional intermediate data structure like a GADT? --> use typed refunctionalization to generate mutually recursive functionals (optimized)
   
  * Generate optimized GADT using MetaOCaml (techinically impossible now)  

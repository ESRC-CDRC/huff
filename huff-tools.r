#########################################################################################################################
#                                                  huff.r                                                               #
#                                                                                                                       #
# Applies the Huff algorithm to calculate the probability of a location patronising a store                             #
# The basic algorithm is Pij = (Aj^a)*(Dij^(-b))/Sum((Aj^a)*(Dij^(-b)))                                                 #
# Where Aj a measure of store attractiveness, Dij the distance from origin i to destination j                           #
# a is the attractiveness parameter, b is the distance parameter                                                        #
#########################################################################################################################

# Load libraries
library(rgdal)
library(rgeos)
library(igraph)
library(FNN)
library(fastshp)
library(dplyr)

#########################################################################################################################
#                                           Select By Number of Neighbours                                              #
#########################################################################################################################
# Uses dplyr package
select_by_neighbours <- function(dist_data_frame, neighbours_constraint){
  return(
    dist_data_frame %>%
      group_by(origins_name) %>%
      arrange(distance) %>%
      mutate(idx = 1:length(origins_name)) %>%
      filter(idx <= neighbours_constraint) %>%
      select(origins_name, destinations_name, distance) %>%
      as.data.frame()
  )
}
#########################################################################################################################
#                                    Select entries by Huff probabilities                                               #
#########################################################################################################################
select_by_probs <- function(huff_probs, nr, origins_name = "origins_name", destinations_name = "destinations_name",
                            distance = "distance", huff_probability = "huff_probability"){
  
  idx <- as.integer(sapply(c(origins_name, destinations_name, distance, huff_probability),
                           function(x) which(names(huff_probs) == x)))
  names(huff_probs)[idx] <- c("origins_name", "destinations_name", "distance", "huff_probability")
  
  return(
    huff_probs %>%
      group_by(origins_name) %>%
      arrange(desc(huff_probability)) %>%
      mutate(idx = 1:length(origins_name)) %>%
      filter(idx <= nr) %>%
      select(origins_name, destinations_name, distance, huff_probability) %>%
      as.data.frame()
  )
}

#########################################################################################################################
#                                  Extract catchments by Huff probabilities                                             #
#########################################################################################################################
get_catchment <- function(poly, path_to_save, shp_name_out, town_centre, huff_prob_upper, huff_prob_lower,
                          origins_name = "origins_name", destinations_name = "destinations_name", huff_probability = "huff_probability"){
  
  ############################################### Functions #############################################################
  select_origins_by_probs <- function(Df, town_centre, n, huff_prob_upper, huff_prob_lower){
    return(
      Df %>%
        mutate(idx = 1:n) %>%
        filter(destinations_name == town_centre) %>%
        filter(huff_probability <= huff_prob_upper & huff_probability > huff_prob_lower) %>%
        select(idx) 
    )
  }
  ########################################################################################################################  
  names_id <- as.integer(sapply(c(origins_name, destinations_name, huff_probability),
                                function(x) which(names(poly) == x)))
  names(poly)[names_id] <- c("origins_name", "destinations_name", "huff_probability")
  
  n <- nrow(poly)
  
  # Get index of selected LSOAs i.e. catchment (selected based on huff prob for a given town centre)
  idx <- select_origins_by_probs(poly@data, town_centre, n, huff_prob_upper, huff_prob_lower)[,1]
  if (length(idx) != 0){
    
    shp_out <- list()
    idx2 <- 1
    polys <- gUnaryUnion(poly[idx, ])@polygons[[1]]@Polygons
    
    for (i in 1:length(polys)){
      if (! polys[[i]]@hole){
        shp_out[[idx2]] <- Polygons(list(Polygon(polys[[i]]@coords)), idx2)
        idx2 <- idx2 + 1
      }
    }
    
    shp_out <- SpatialPolygonsDataFrame(SpatialPolygons(shp_out), data.frame(destination = rep(town_centre, idx2-1)))
    # Project
    proj4string(shp_out) <- proj4string(poly)
    # Save
    writeOGR(shp_out, path_to_save, shp_name_out, driver = "ESRI Shapefile")
    #plot(shp_out)
  }
}

#########################################################################################################################
#                                      Convert polygon boundaries to points                                             #
#########################################################################################################################
polygons_to_points <- function(polys, field_name, rm_holes=T){
  
  ############################################################ Functions #######################################################################
  if (rm_holes){
    get_coords <- function(polys, idx){
      return(do.call("cbind", list(do.call("rbind", lapply(polys@Polygons, function(poly) if (!poly@hole) poly@coords)), idx)))
    }
  } else {
    get_coords <- function(polys, idx){
      return(do.call("cbind", list(do.call("rbind", lapply(polys@Polygons, function(poly) poly@coords)), idx)))
    }
  }  
  ##############################################################################################################################################
  if (nrow(polys) > 1){
    out <- do.call("rbind", mapply(get_coords, polys@polygons, 1:nrow(polys)))
  } else {
    out <- get_coords(polys@polygons[[1]], 1)
  } 
  
  polys@data[[field_name]] <- as.character(polys@data[[field_name]])
  
  out <- as.data.frame(out)
  names(out) <- c("easting", "northing", "idx")
  out <- inner_join(out, data.frame(idx = 1:nrow(polys), Names = polys@data[[field_name]], stringsAsFactors = F), by = "idx") 
  out$idx <- NULL
  coordinates(out) =~ easting + northing
  proj4string(out) <- proj4string(polys)
  
  return(out)
}

#########################################################################################################################
#                                      Get connected parts of the road network                                          #
#########################################################################################################################
get_connected <- function(path_to_shp, shp_name_in, path_to_save = "None", shp_name_out = "None", plot_output = F){
  
  ############################################### Functions #############################################################
  get_edges <- function(roads_list){
    n <- length(roads_list$x)
    return(do.call("cbind", list(paste(roads_list$x[1], roads_list$y[1]), paste(roads_list$x[n], roads_list$y[n]))))
  }
  
  convert_to_SpatialLinesDF <- function(roads_list, proj4roads){
    lines_sp <- vector("list", length(roads_list))
    for (i in 1:length(lines_sp)){
      lines_sp[[i]] <- Lines(list(Line(cbind(roads_list[[i]]$x, roads_list[[i]]$y))), as.character(i))
    }
    return(SpatialLinesDataFrame(SpatialLines(lines_sp, proj4string = CRS(proj4roads)), data.frame(ID = 1:length(lines_sp))))
  }
  ########################################################################################################################
  roads <- read.shp(paste(path_to_shp, "/", shp_name_in, ".shp", sep = ""), "list")
  proj4roads <- ogrInfo(path_to_shp, shp_name_in)$p4s
  
  edges <- do.call("rbind", lapply(roads, get_edges))  
  roads_graph <- graph.edgelist(edges, directed = FALSE)
  # Decompose the graph to connected parts, the result is a list
  # The first element of the list has the most vertices 
  graph_parts <- decompose.graph(roads_graph)
  
  if (length(graph_parts) > 1){
    # Find road part with the highest number of vertices 
    vertices <- V(graph_parts[[which.max(sapply(1:length(graph_parts), function(x) length(V(graph_parts[[x]]))))]])$name
    # Map selected road part vertices to road network edges
    idxs <- unique(c(which(edges[,1] %in% vertices), which(edges[,2] %in% vertices)))
    
    print(paste("There are", length(graph_parts), "unconnected parts in the road network"))
    # Extract most strongly connected road part
    out <- roads[idxs]
    
    if (path_to_save != "None" & shp_name_out != "None"){
      connected <- convert_to_SpatialLinesDF(out, proj4roads)
      writeOGR(connected, path_to_save, shp_name_out, driver = "ESRI Shapefile")
      if (plot_output){
        plot(connected)
        lines(convert_to_SpatialLinesDF(roads[-idxs]), col = "red", lwd = 1.5)
        title(main = paste("There are", length(graph_parts), "unconnected parts in the road network"),
              sub = "Lines marked with red were removed")
      }  
    }
    else if (plot_output){
      connected <- convert_to_SpatialLinesDF(out, proj4roads)
      plot(connected)
      lines(convert_to_SpatialLinesDF(roads[-idxs]), col = "red", lwd = 1.5)
      title(main = paste("There are", length(graph_parts), "unconnected parts in the road network"),
            sub = "Lines marked with red were removed")
    }
    return(out)
  }  
  else {
    print("There are no unconnected parts in the road network")
    return(roads)
  }
}

#########################################################################################################################
#                                  Function to check distance-related inputs                                            #
#########################################################################################################################
check_distance_inputs <- function(destinations, destinations_name, origins, origins_name,
                                  neighbours_constraint = "None", distance_constraint = "None"){
  
  destinations_nr <- nrow(destinations@data)
  origins_nr <- nrow(origins@data)
  
  if (any(is.na(destinations@data))){
    stop("NA values were found in the destinations data")
  }
  
  if (any(is.na(destinations_name))){
    stop("NA values were found in the destinations names")
  }
  
  if (any(is.na(origins@data))){
    stop("NA values were found in the origins data")
  }
  
  if (any(is.na(origins_name))){
    stop("NA values were found in the origins names")
  }
  
  if (! identical(destinations@proj4string, origins@proj4string)){
    warning("Destination and Origin locations are not in the same coordinate system")
  }
  
  if (length(destinations_name) != destinations_nr){
    stop("Provide a name for each destination")
  }
  
  # The origins_name vector is not optional
  if (length(origins_name) != origins_nr){
    stop("Provide a name for each origin location")
  }
  
  # If duplicates in destinations names flag = T
  if (anyDuplicated(destinations_name) != 0){
    destinations_flag = T
  } else {
    destinations_flag = F
  }
  
  # Origin names should be unique though
  if (anyDuplicated(origins_name) != 0){
    stop("Provide a unique name for each origin location")
  }
  
  # Neighbour constraint value should br greater than 1 or None
  if (neighbours_constraint != "None"){
    if (length(neighbours_constraint) > 1){
      stop("Provide a unique value for the neighbours contraint")
    } else if (neighbours_constraint < 1){
      stop("Give a valid value for the neighbours constraint")
    } else if (neighbours_constraint > destinations_nr){
      stop("Neighbours constraint greater than the number of destinations")
    }
  }
  
  # Distance constraint value should be greater than 1 or None
  if (distance_constraint != "None"){
    if (length(distance_constraint) > 1){
      stop("Provide a unique value for the distance contraint")
    } else if (distance_constraint < 1){
      stop("Give a valid value for the distance constraint")
    }
  }
  return(c(destinations_nr, origins_nr, destinations_flag))
}

#########################################################################################################################
#                                 Function to check the arguments of the huff function                                  #
#########################################################################################################################
check_huff <- function(destinations_name, destinations_attractiveness, origins_name, distance, alpha, beta){
  
  destinations_nr <- length(destinations_name)
  
  if (any(is.na(destinations_name))){
    stop("NA values were found in the destinations names")
  }
  
  if (any(is.na(destinations_attractiveness))){
    stop("NA values were found in the attractiveness data")
  }
  
  if (any(is.na(origins_name))){
    stop("NA values were found in the origins names")
  }
  
  if (any(is.na(distance))){
    stop("NA values were found the distance data")
  }
  
  if (any(is.na(alpha))){
    stop("NA values were found in the alpha exponent")
  }
  
  if (any(is.na(beta))){
    stop("NA values were found in the beta exponent")
  }
  
  # The destinations_attractiveness vector should be of equal length to the destinations data
  if (length(destinations_attractiveness) != destinations_nr){
    stop("The destinations_attractiveness vector should be the same length as the destinations_name")
  }
  
  if (length(origins_name) != destinations_nr){
    stop("The origins_name vector should be the same length as the destinations_name")
  }
  
  if (length(distance) != destinations_nr){
    stop("The distance vector should be the same length as the destinations_name")
  }
  
  if (any(distance <= 0)){
    dist_flag = T # True means do sth with distance, i.e. replace zeroes
    warning("Distances equal to zero were found, all distances below 0.1 were replaced with 0.1")
  } else {
    dist_flag = F
  }
  
  # Are there any weird values in the destinations_attractiveness vector
  if (min(destinations_attractiveness) <= 0){
    stop("The attractiveness score can't be less than or equal to zero")
  }
  
  # The same for alpha
  if (length(alpha) > 1){
    if (min(alpha) < 0){
      stop("The alpha value should be greater than or equal to zero")
    } else if (length(alpha) != destinations_nr){
      stop("Different lengths between vectors of alpha values and destinations, should be equal")
    }
    alpha_flag = F
  } else {
    if (alpha < 0 || length(alpha) == 0){
      stop("The alpha value should be greater or equal to zero")
    } else {
      alpha_flag = T # True means do sth with alpha that is get from length 1 to length n as follows
      # alpha <- rep(alpha, destinations_nr)
    }
  }
  
  # The same for beta
  if (length(beta) > 1){
    if (min(beta) < 0){
      stop("The beta value should be greater than or equal to zero")
    } else if (length(beta) != destinations_nr){
      stop("Different length for the vectors of beta values and destinations was provided, should be equal")
    }
    beta_flag = F
  } else {
    if (beta < 0 || length(beta) == 0){
      stop("The beta value should be greater or equal to zero")
    } else {
      beta_flag = T # True means do sth with beta that is get from length 1 to length n as follows
      # beta <- rep(beta, destinations_nr)
    }
  }
  return(c(destinations_nr, alpha_flag, beta_flag, dist_flag))
}

#########################################################################################################################
#                                           Euclidean distance                                                          #
#########################################################################################################################
euclidean_distance <- function(destinations, destinations_name, origins, origins_name, 
                               neighbours_constraint = "None", distance_constraint = "None"){
  
  ############################################ Check inputs #############################################################
  shp_nrows <- check_distance_inputs(destinations, destinations_name, origins, origins_name,
                                     neighbours_constraint, distance_constraint)
  
  if (shp_nrows[3]){
    stop("Duplicate names were found for destinations")
  }
  
  destinations_name <- as.character(destinations_name)
  origins_name <- as.character(origins_name)
  
  ############################################ Main Function ############################################################
  # Calculate Euclidean distance with gDistance function from rgeos
  distance <- as.numeric(t(gDistance(destinations, origins, byid = T))) / 1000
  
  out <- data.frame(origins_name = as.character(sapply(origins_name, rep, shp_nrows[1])), 
                    destinations_name = rep(destinations_name, shp_nrows[2]), distance = distance, stringsAsFactors = F)
  
  if (distance_constraint != "None"){
    out <- out[out$distance < distance_constraint, ]
  }
  
  if (neighbours_constraint != "None"){
    out <- select_by_neighbours(out, neighbours_constraint)
  }
  
  return(out)
}
#########################################################################################################################
#                                            Shortest Distance                                                          #
#########################################################################################################################
shortest_distance <- function(destinations, destinations_name, origins, origins_name, roads,
                              neighbours_constraint = "None", distance_constraint = "None"){
  
  ############################################# Functions ###############################################################
  get_nodes <- function(roads_list){
    n <- length(roads_list$x)
    return(do.call("cbind", list(roads_list$x[-n], roads_list$y[-n], roads_list$x[-1], roads_list$y[-1])))
  }
    
  ############################################ Check inputs #############################################################
  flags <- check_distance_inputs(destinations, destinations_name, origins, origins_name,
                               neighbours_constraint, distance_constraint)
  
  destinations_name <- as.character(destinations_name)
  origins_name <- as.character(origins_name)
  
  ######################### Run the main body of the function with igraph ###############################################
  # Build a matrix with column 1 providing x_1, column 2 y_1, column 3 x_2 and column 4 y_2
  nodes <- do.call("rbind", lapply(roads, get_nodes))
  
  # To build the graph, we need a matrix with two columns of characters, the first is the start (x,y) the second is the end (x,y)
  igraph_object <- graph.edgelist(cbind(paste(nodes[,1], nodes[,2]), paste(nodes[,3], nodes[,4])), directed = FALSE)
  
  # Weight graph by road segment length
  E(igraph_object)$weight <- sqrt((nodes[, 1] - nodes[, 3])^2 + (nodes[, 2] - nodes[, 4])^2) / 1000
  
  xy <- do.call(rbind, strsplit(V(igraph_object)$name, " "))
  #     V(igraph_object)$x <- as.numeric(xy[,1])
  #     V(igraph_object)$y <- as.numeric(xy[,2])
  
  # Convert entries of matrix from character to numeric
  storage.mode(xy) <- "numeric"
  # Map origin and destination nodes to closest nodes
  origins_id <- get.knnx(xy, coordinates(origins), 1)$nn.index[,1]
  destinations_id <- get.knnx(xy, coordinates(destinations), 1)$nn.index[,1]
  
  # If we don't have duplicate origin IDs we can run the shortest.paths function
  if (anyDuplicated(origins_id) == 0){
    # If we don't have neighbours constraint
    # flags[1] gives the number of rows of destinations and flags[2] gives the number of rows of origins
    out <- data.frame(origins_name = rep(origins_name, flags[1]), destinations_name = as.character(sapply(destinations_name, rep, flags[2])),
                      distance = rep(NA, flags[2] * flags[1]), stringsAsFactors = F)
    for (i in 0:(flags[1] - 1)){
      out[(i * flags[2] + 1):((i + 1) * flags[2]), "distance"] <- as.numeric(shortest.paths(igraph_object, v = destinations_id[i+1], to = origins_id))
    }
    
  } else {
    # If we have duplicate origins select unique origins to calculate the distance to
    unique_origins_id <- unique(origins_id)
    # we will merge the unique origins with the complete set of origins
    out <- data.frame(origins_name = rep("None", flags[1] * flags[2]), destinations_name = as.character(sapply(destinations_name, rep, flags[2])),
                      distance = rep(NA, flags[2] * flags[1]), stringsAsFactors = F)
    for (i in 0:(flags[1] - 1)){
      out[(i * flags[2] + 1):((i + 1) * flags[2]), c(1,3)] <- inner_join(data.frame(origins_id = origins_id, origins_name = origins_name, stringsAsFactors = F),
                                                                    data.frame(origins_id = unique_origins_id, distance =
                                                                                 as.numeric(shortest.paths(igraph_object, v = destinations_id[i+1], to = unique_origins_id))),
                                                                    sort = F, stringsAsFactors = F)[,2:3]
    }
  }
  
  if (distance_constraint != "None"){
    out <- out[out$distance < distance_constraint, ]
  }
  
  if (neighbours_constraint != "None"){
    out <- select_by_neighbours(out, neighbours_constraint)
  }
  
  if (flags[3]){
    warning("Duplicate destinations will be treated as groups of points")
    out <- out %>% 
      group_by(destinations_name, origins_name) %>%
      summarize(min(distance)) %>%
      as.data.frame()
  }
  
  return(out)
}


#########################################################################################################################
#                                            Basic Huff Function                                                        #
#########################################################################################################################

huff_basic <- function(destinations_name, destinations_attractiveness, origins_name, distance, alpha = 1, beta = 2){
  
  ############################################### Functions #############################################################
  huff_numerator_basic <- function(destinations_attractiveness, alpha, distance, beta){
    return((destinations_attractiveness ^ alpha) / (distance ^ beta))
  }
  
  ########################################### Check arguments ###########################################################
  flags <- check_huff(destinations_name, destinations_attractiveness, origins_name, distance, alpha, beta)
  # If we have distance values equal to zero replace with 0.1 (assuming distance in Km)
  
  if (flags[2]){
    alpha <- rep(alpha, flags[1])
  }
  
  if (flags[3]){
    beta <- rep(beta, flags[1])
  }
  
  if (flags[4]){
    distance <- ifelse(distance < 0.1, 0.1, distance)
  }
  
  ################################### Calculate Huff's (basic) algorithm ################################################
  # Numerator, calculated using the huff_numerator_basic function
  huff <- mapply(huff_numerator_basic, destinations_attractiveness, alpha, distance, beta) 
  
  # Denominator of the basic huff algorithm
  sum_huff_location <- aggregate(huff, by = list(origins_name), sum)
  names(sum_huff_location) <- c("origins_name", "sum_huff")
  
  # Merge denominator and numerator
  out <- inner_join(data.frame(origins_name, destinations_name, distance, huff), sum_huff_location) 
  
  # Calculate huff probabilities
  out$huff_probability <- with(out, huff / sum_huff)
  
  return(out)
}


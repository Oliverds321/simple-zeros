import R11111_Leaves0
import R11111_Leaves1
import R11111_Leaves2
import R11111_Leaves3
import R11111_Leaves4
import R11111_Leaves5
import R11111_Leaves6
import R11111_Leaves7
import R11111_Leaves8
import R11111_Leaves9
import R11111_Leaves10
import R11111_Leaves11
import R11111_Leaves12
import R11111_Leaves13
import R11111_Leaves14
import R11111_Leaves15
import R11111_Leaves16
import R11111_Leaves17
import R11111_Leaves18
import R11111_Leaves19
import R11111_Leaves20
import R11111_Leaves21
import R11111_Leaves22
import R11111_Leaves23
import R11111_Leaves24
import R11111_Leaves25
import R11111_Leaves26
import R11111_Leaves27
import R11111_Leaves28
import R11111_Leaves29
import R11111_Leaves30
import R11111_Leaves31
import R11111_Leaves32
import R11111_Leaves33
import R11111_Leaves34
import R11111_Leaves35
import R11111_Leaves36
import R11111_Leaves37
import R11111_Leaves38
import R11111_Leaves39
import R11111_Leaves40
import R11111_Leaves41
import R11111_Leaves42
import R11111_Leaves43

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R11111

def T3448 : Node := Node.leaf L3448
theorem T3448_ok : Node.check D_R11111 T3448 [((535/128),(535/64)),((0),(333/64)),((0),(333/64)),((535/128),(535/64))] = true := Node.check_leaf_of _ _ _ L3448_ok
def T3447 : Node := Node.leaf L3447
theorem T3447_ok : Node.check D_R11111 T3447 [((535/128),(535/64)),((333/128),(333/64)),((0),(333/64)),((0),(535/128))] = true := Node.check_leaf_of _ _ _ L3447_ok
def T3446 : Node := Node.leaf L3446
theorem T3446_ok : Node.check D_R11111 T3446 [((535/128),(535/64)),((0),(333/128)),((333/128),(333/64)),((0),(535/128))] = true := Node.check_leaf_of _ _ _ L3446_ok
def T3445 : Node := Node.leaf L3445
theorem T3445_ok : Node.check D_R11111 T3445 [((1605/256),(535/64)),((0),(333/128)),((0),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3445_ok
def T3444 : Node := Node.leaf L3444
theorem T3444_ok : Node.check D_R11111 T3444 [((1605/256),(535/64)),((333/256),(333/128)),((0),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3444_ok
def T3443 : Node := Node.leaf L3443
theorem T3443_ok : Node.check D_R11111 T3443 [((1605/256),(535/64)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3443_ok
def T3442 : Node := Node.leaf L3442
theorem T3442_ok : Node.check D_R11111 T3442 [((3745/512),(535/64)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3442_ok
def T3441 : Node := Node.leaf L3441
theorem T3441_ok : Node.check D_R11111 T3441 [((3745/512),(535/64)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3441_ok
def T3440 : Node := Node.leaf L3440
theorem T3440_ok : Node.check D_R11111 T3440 [((3745/512),(535/64)),((0),(333/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3440_ok
def T3439 : Node := Node.leaf L3439
theorem T3439_ok : Node.check D_R11111 T3439 [((8025/1024),(535/64)),((0),(333/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3439_ok
def T3438 : Node := Node.leaf L3438
theorem T3438_ok : Node.check D_R11111 T3438 [((8025/1024),(535/64)),((333/1024),(333/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3438_ok
def T3437 : Node := Node.leaf L3437
theorem T3437_ok : Node.check D_R11111 T3437 [((8025/1024),(535/64)),((0),(333/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3437_ok
def T3436 : Node := Node.leaf L3436
theorem T3436_ok : Node.check D_R11111 T3436 [((16585/2048),(535/64)),((0),(333/1024)),((0),(333/1024)),((535/2048),(535/1024))] = true := Node.check_leaf_of _ _ _ L3436_ok
def T3435 : Node := Node.leaf L3435
theorem T3435_ok : Node.check D_R11111 T3435 [((16585/2048),(535/64)),((0),(333/1024)),((0),(333/1024)),((0),(535/2048))] = true := Node.check_leaf_of _ _ _ L3435_ok
def T3434 : Node := Node.split 3 T3435 T3436
theorem T3434_ok : Node.check D_R11111 T3434 [((16585/2048),(535/64)),((0),(333/1024)),((0),(333/1024)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3435_ok T3436_ok
def T3433 : Node := Node.leaf L3433
theorem T3433_ok : Node.check D_R11111 T3433 [((8025/1024),(16585/2048)),((0),(333/1024)),((0),(333/1024)),((535/2048),(535/1024))] = true := Node.check_leaf_of _ _ _ L3433_ok
def T3432 : Node := Node.leaf L3432
theorem T3432_ok : Node.check D_R11111 T3432 [((8025/1024),(16585/2048)),((0),(333/1024)),((0),(333/1024)),((0),(535/2048))] = true := Node.check_leaf_of _ _ _ L3432_ok
def T3431 : Node := Node.split 3 T3432 T3433
theorem T3431_ok : Node.check D_R11111 T3431 [((8025/1024),(16585/2048)),((0),(333/1024)),((0),(333/1024)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3432_ok T3433_ok
def T3430 : Node := Node.split 0 T3431 T3434
theorem T3430_ok : Node.check D_R11111 T3430 [((8025/1024),(535/64)),((0),(333/1024)),((0),(333/1024)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3431_ok T3434_ok
def T3429 : Node := Node.split 2 T3430 T3437
theorem T3429_ok : Node.check D_R11111 T3429 [((8025/1024),(535/64)),((0),(333/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3430_ok T3437_ok
def T3428 : Node := Node.split 1 T3429 T3438
theorem T3428_ok : Node.check D_R11111 T3428 [((8025/1024),(535/64)),((0),(333/512)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3429_ok T3438_ok
def T3427 : Node := Node.split 3 T3428 T3439
theorem T3427_ok : Node.check D_R11111 T3427 [((8025/1024),(535/64)),((0),(333/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3428_ok T3439_ok
def T3426 : Node := Node.leaf L3426
theorem T3426_ok : Node.check D_R11111 T3426 [((3745/512),(8025/1024)),((333/1024),(333/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3426_ok
def T3425 : Node := Node.leaf L3425
theorem T3425_ok : Node.check D_R11111 T3425 [((3745/512),(8025/1024)),((0),(333/1024)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3425_ok
def T3424 : Node := Node.split 1 T3425 T3426
theorem T3424_ok : Node.check D_R11111 T3424 [((3745/512),(8025/1024)),((0),(333/512)),((0),(333/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3425_ok T3426_ok
def T3423 : Node := Node.leaf L3423
theorem T3423_ok : Node.check D_R11111 T3423 [((3745/512),(8025/1024)),((0),(333/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3423_ok
def T3422 : Node := Node.split 3 T3423 T3424
theorem T3422_ok : Node.check D_R11111 T3422 [((3745/512),(8025/1024)),((0),(333/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3423_ok T3424_ok
def T3421 : Node := Node.split 0 T3422 T3427
theorem T3421_ok : Node.check D_R11111 T3421 [((3745/512),(535/64)),((0),(333/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3422_ok T3427_ok
def T3420 : Node := Node.split 2 T3421 T3440
theorem T3420_ok : Node.check D_R11111 T3420 [((3745/512),(535/64)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3421_ok T3440_ok
def T3419 : Node := Node.split 1 T3420 T3441
theorem T3419_ok : Node.check D_R11111 T3419 [((3745/512),(535/64)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3420_ok T3441_ok
def T3418 : Node := Node.split 3 T3419 T3442
theorem T3418_ok : Node.check D_R11111 T3418 [((3745/512),(535/64)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3419_ok T3442_ok
def T3417 : Node := Node.leaf L3417
theorem T3417_ok : Node.check D_R11111 T3417 [((1605/256),(3745/512)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3417_ok
def T3416 : Node := Node.leaf L3416
theorem T3416_ok : Node.check D_R11111 T3416 [((1605/256),(3745/512)),((0),(333/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3416_ok
def T3415 : Node := Node.leaf L3415
theorem T3415_ok : Node.check D_R11111 T3415 [((1605/256),(3745/512)),((0),(333/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3415_ok
def T3414 : Node := Node.split 2 T3415 T3416
theorem T3414_ok : Node.check D_R11111 T3414 [((1605/256),(3745/512)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3415_ok T3416_ok
def T3413 : Node := Node.split 1 T3414 T3417
theorem T3413_ok : Node.check D_R11111 T3413 [((1605/256),(3745/512)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3414_ok T3417_ok
def T3412 : Node := Node.leaf L3412
theorem T3412_ok : Node.check D_R11111 T3412 [((1605/256),(3745/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3412_ok
def T3411 : Node := Node.leaf L3411
theorem T3411_ok : Node.check D_R11111 T3411 [((6955/1024),(3745/512)),((333/512),(333/256)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3411_ok
def T3410 : Node := Node.leaf L3410
theorem T3410_ok : Node.check D_R11111 T3410 [((6955/1024),(3745/512)),((999/1024),(333/256)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3410_ok
def T3409 : Node := Node.leaf L3409
theorem T3409_ok : Node.check D_R11111 T3409 [((6955/1024),(3745/512)),((333/512),(999/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3409_ok
def T3408 : Node := Node.leaf L3408
theorem T3408_ok : Node.check D_R11111 T3408 [((6955/1024),(3745/512)),((333/512),(999/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3408_ok
def T3407 : Node := Node.split 2 T3408 T3409
theorem T3407_ok : Node.check D_R11111 T3407 [((6955/1024),(3745/512)),((333/512),(999/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3408_ok T3409_ok
def T3406 : Node := Node.split 1 T3407 T3410
theorem T3406_ok : Node.check D_R11111 T3406 [((6955/1024),(3745/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3407_ok T3410_ok
def T3405 : Node := Node.split 3 T3406 T3411
theorem T3405_ok : Node.check D_R11111 T3405 [((6955/1024),(3745/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3406_ok T3411_ok
def T3404 : Node := Node.leaf L3404
theorem T3404_ok : Node.check D_R11111 T3404 [((1605/256),(6955/1024)),((333/512),(333/256)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3404_ok
def T3403 : Node := Node.leaf L3403
theorem T3403_ok : Node.check D_R11111 T3403 [((1605/256),(6955/1024)),((333/512),(333/256)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3403_ok
def T3402 : Node := Node.split 3 T3403 T3404
theorem T3402_ok : Node.check D_R11111 T3402 [((1605/256),(6955/1024)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3403_ok T3404_ok
def T3401 : Node := Node.split 0 T3402 T3405
theorem T3401_ok : Node.check D_R11111 T3401 [((1605/256),(3745/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3402_ok T3405_ok
def T3400 : Node := Node.split 2 T3401 T3412
theorem T3400_ok : Node.check D_R11111 T3400 [((1605/256),(3745/512)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3401_ok T3412_ok
def T3399 : Node := Node.leaf L3399
theorem T3399_ok : Node.check D_R11111 T3399 [((1605/256),(3745/512)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3399_ok
def T3398 : Node := Node.split 1 T3399 T3400
theorem T3398_ok : Node.check D_R11111 T3398 [((1605/256),(3745/512)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3399_ok T3400_ok
def T3397 : Node := Node.split 3 T3398 T3413
theorem T3397_ok : Node.check D_R11111 T3397 [((1605/256),(3745/512)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3398_ok T3413_ok
def T3396 : Node := Node.split 0 T3397 T3418
theorem T3396_ok : Node.check D_R11111 T3396 [((1605/256),(535/64)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3397_ok T3418_ok
def T3395 : Node := Node.split 2 T3396 T3443
theorem T3395_ok : Node.check D_R11111 T3395 [((1605/256),(535/64)),((0),(333/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3396_ok T3443_ok
def T3394 : Node := Node.split 1 T3395 T3444
theorem T3394_ok : Node.check D_R11111 T3394 [((1605/256),(535/64)),((0),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3395_ok T3444_ok
def T3393 : Node := Node.split 3 T3394 T3445
theorem T3393_ok : Node.check D_R11111 T3393 [((1605/256),(535/64)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3394_ok T3445_ok
def T3392 : Node := Node.leaf L3392
theorem T3392_ok : Node.check D_R11111 T3392 [((535/128),(1605/256)),((333/256),(333/128)),((0),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3392_ok
def T3391 : Node := Node.leaf L3391
theorem T3391_ok : Node.check D_R11111 T3391 [((535/128),(1605/256)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3391_ok
def T3390 : Node := Node.leaf L3390
theorem T3390_ok : Node.check D_R11111 T3390 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3390_ok
def T3389 : Node := Node.leaf L3389
theorem T3389_ok : Node.check D_R11111 T3389 [((2675/512),(1605/256)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3389_ok
def T3388 : Node := Node.leaf L3388
theorem T3388_ok : Node.check D_R11111 T3388 [((2675/512),(1605/256)),((0),(333/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3388_ok
def T3387 : Node := Node.leaf L3387
theorem T3387_ok : Node.check D_R11111 T3387 [((2675/512),(1605/256)),((0),(333/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3387_ok
def T3386 : Node := Node.split 2 T3387 T3388
theorem T3386_ok : Node.check D_R11111 T3386 [((2675/512),(1605/256)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3387_ok T3388_ok
def T3385 : Node := Node.split 1 T3386 T3389
theorem T3385_ok : Node.check D_R11111 T3385 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3386_ok T3389_ok
def T3384 : Node := Node.split 3 T3385 T3390
theorem T3384_ok : Node.check D_R11111 T3384 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3385_ok T3390_ok
def T3383 : Node := Node.leaf L3383
theorem T3383_ok : Node.check D_R11111 T3383 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3383_ok
def T3382 : Node := Node.leaf L3382
theorem T3382_ok : Node.check D_R11111 T3382 [((535/128),(2675/512)),((0),(333/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3382_ok
def T3381 : Node := Node.leaf L3381
theorem T3381_ok : Node.check D_R11111 T3381 [((535/128),(2675/512)),((0),(333/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3381_ok
def T3380 : Node := Node.split 2 T3381 T3382
theorem T3380_ok : Node.check D_R11111 T3380 [((535/128),(2675/512)),((0),(333/512)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3381_ok T3382_ok
def T3379 : Node := Node.split 1 T3380 T3383
theorem T3379_ok : Node.check D_R11111 T3379 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3380_ok T3383_ok
def T3378 : Node := Node.leaf L3378
theorem T3378_ok : Node.check D_R11111 T3378 [((535/128),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3378_ok
def T3377 : Node := Node.leaf L3377
theorem T3377_ok : Node.check D_R11111 T3377 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3377_ok
def T3376 : Node := Node.split 2 T3377 T3378
theorem T3376_ok : Node.check D_R11111 T3376 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3377_ok T3378_ok
def T3375 : Node := Node.leaf L3375
theorem T3375_ok : Node.check D_R11111 T3375 [((535/128),(2675/512)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3375_ok
def T3374 : Node := Node.split 1 T3375 T3376
theorem T3374_ok : Node.check D_R11111 T3374 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3375_ok T3376_ok
def T3373 : Node := Node.split 3 T3374 T3379
theorem T3373_ok : Node.check D_R11111 T3373 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3374_ok T3379_ok
def T3372 : Node := Node.split 0 T3373 T3384
theorem T3372_ok : Node.check D_R11111 T3372 [((535/128),(1605/256)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3373_ok T3384_ok
def T3371 : Node := Node.split 2 T3372 T3391
theorem T3371_ok : Node.check D_R11111 T3371 [((535/128),(1605/256)),((0),(333/256)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3372_ok T3391_ok
def T3370 : Node := Node.split 1 T3371 T3392
theorem T3370_ok : Node.check D_R11111 T3370 [((535/128),(1605/256)),((0),(333/128)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3371_ok T3392_ok
def T3369 : Node := Node.leaf L3369
theorem T3369_ok : Node.check D_R11111 T3369 [((535/128),(1605/256)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3369_ok
def T3368 : Node := Node.leaf L3368
theorem T3368_ok : Node.check D_R11111 T3368 [((2675/512),(1605/256)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3368_ok
def T3367 : Node := Node.leaf L3367
theorem T3367_ok : Node.check D_R11111 T3367 [((2675/512),(1605/256)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3367_ok
def T3366 : Node := Node.leaf L3366
theorem T3366_ok : Node.check D_R11111 T3366 [((2675/512),(1605/256)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3366_ok
def T3365 : Node := Node.leaf L3365
theorem T3365_ok : Node.check D_R11111 T3365 [((5885/1024),(1605/256)),((333/256),(999/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3365_ok
def T3364 : Node := Node.leaf L3364
theorem T3364_ok : Node.check D_R11111 T3364 [((5885/1024),(1605/256)),((1665/1024),(999/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3364_ok
def T3363 : Node := Node.leaf L3363
theorem T3363_ok : Node.check D_R11111 T3363 [((5885/1024),(1605/256)),((333/256),(1665/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3363_ok
def T3362 : Node := Node.leaf L3362
theorem T3362_ok : Node.check D_R11111 T3362 [((5885/1024),(1605/256)),((333/256),(1665/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3362_ok
def T3361 : Node := Node.split 2 T3362 T3363
theorem T3361_ok : Node.check D_R11111 T3361 [((5885/1024),(1605/256)),((333/256),(1665/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3362_ok T3363_ok
def T3360 : Node := Node.split 1 T3361 T3364
theorem T3360_ok : Node.check D_R11111 T3360 [((5885/1024),(1605/256)),((333/256),(999/512)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3361_ok T3364_ok
def T3359 : Node := Node.split 3 T3360 T3365
theorem T3359_ok : Node.check D_R11111 T3359 [((5885/1024),(1605/256)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3360_ok T3365_ok
def T3358 : Node := Node.leaf L3358
theorem T3358_ok : Node.check D_R11111 T3358 [((2675/512),(5885/1024)),((333/256),(999/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3358_ok
def T3357 : Node := Node.leaf L3357
theorem T3357_ok : Node.check D_R11111 T3357 [((2675/512),(5885/1024)),((333/256),(999/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3357_ok
def T3356 : Node := Node.split 3 T3357 T3358
theorem T3356_ok : Node.check D_R11111 T3356 [((2675/512),(5885/1024)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3357_ok T3358_ok
def T3355 : Node := Node.split 0 T3356 T3359
theorem T3355_ok : Node.check D_R11111 T3355 [((2675/512),(1605/256)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3356_ok T3359_ok
def T3354 : Node := Node.split 2 T3355 T3366
theorem T3354_ok : Node.check D_R11111 T3354 [((2675/512),(1605/256)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3355_ok T3366_ok
def T3353 : Node := Node.split 1 T3354 T3367
theorem T3353_ok : Node.check D_R11111 T3353 [((2675/512),(1605/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3354_ok T3367_ok
def T3352 : Node := Node.split 3 T3353 T3368
theorem T3352_ok : Node.check D_R11111 T3352 [((2675/512),(1605/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3353_ok T3368_ok
def T3351 : Node := Node.leaf L3351
theorem T3351_ok : Node.check D_R11111 T3351 [((535/128),(2675/512)),((999/512),(333/128)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3351_ok
def T3350 : Node := Node.leaf L3350
theorem T3350_ok : Node.check D_R11111 T3350 [((535/128),(2675/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3350_ok
def T3349 : Node := Node.leaf L3349
theorem T3349_ok : Node.check D_R11111 T3349 [((535/128),(2675/512)),((333/256),(999/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3349_ok
def T3348 : Node := Node.split 2 T3349 T3350
theorem T3348_ok : Node.check D_R11111 T3348 [((535/128),(2675/512)),((333/256),(999/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3349_ok T3350_ok
def T3347 : Node := Node.split 1 T3348 T3351
theorem T3347_ok : Node.check D_R11111 T3347 [((535/128),(2675/512)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3348_ok T3351_ok
def T3346 : Node := Node.leaf L3346
theorem T3346_ok : Node.check D_R11111 T3346 [((535/128),(2675/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3346_ok
def T3345 : Node := Node.leaf L3345
theorem T3345_ok : Node.check D_R11111 T3345 [((4815/1024),(2675/512)),((999/512),(333/128)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3345_ok
def T3344 : Node := Node.leaf L3344
theorem T3344_ok : Node.check D_R11111 T3344 [((4815/1024),(2675/512)),((2331/1024),(333/128)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3344_ok
def T3343 : Node := Node.leaf L3343
theorem T3343_ok : Node.check D_R11111 T3343 [((4815/1024),(2675/512)),((999/512),(2331/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3343_ok
def T3342 : Node := Node.leaf L3342
theorem T3342_ok : Node.check D_R11111 T3342 [((4815/1024),(2675/512)),((999/512),(2331/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3342_ok
def T3341 : Node := Node.split 2 T3342 T3343
theorem T3341_ok : Node.check D_R11111 T3341 [((4815/1024),(2675/512)),((999/512),(2331/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3342_ok T3343_ok
def T3340 : Node := Node.split 1 T3341 T3344
theorem T3340_ok : Node.check D_R11111 T3340 [((4815/1024),(2675/512)),((999/512),(333/128)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3341_ok T3344_ok
def T3339 : Node := Node.split 3 T3340 T3345
theorem T3339_ok : Node.check D_R11111 T3339 [((4815/1024),(2675/512)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3340_ok T3345_ok
def T3338 : Node := Node.leaf L3338
theorem T3338_ok : Node.check D_R11111 T3338 [((535/128),(4815/1024)),((999/512),(333/128)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3338_ok
def T3337 : Node := Node.leaf L3337
theorem T3337_ok : Node.check D_R11111 T3337 [((535/128),(4815/1024)),((999/512),(333/128)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3337_ok
def T3336 : Node := Node.split 3 T3337 T3338
theorem T3336_ok : Node.check D_R11111 T3336 [((535/128),(4815/1024)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3337_ok T3338_ok
def T3335 : Node := Node.split 0 T3336 T3339
theorem T3335_ok : Node.check D_R11111 T3335 [((535/128),(2675/512)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3336_ok T3339_ok
def T3334 : Node := Node.split 2 T3335 T3346
theorem T3334_ok : Node.check D_R11111 T3334 [((535/128),(2675/512)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3335_ok T3346_ok
def T3333 : Node := Node.leaf L3333
theorem T3333_ok : Node.check D_R11111 T3333 [((4815/1024),(2675/512)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3333_ok
def T3332 : Node := Node.leaf L3332
theorem T3332_ok : Node.check D_R11111 T3332 [((4815/1024),(2675/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3332_ok
def T3331 : Node := Node.split 3 T3332 T3333
theorem T3331_ok : Node.check D_R11111 T3331 [((4815/1024),(2675/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3332_ok T3333_ok
def T3330 : Node := Node.leaf L3330
theorem T3330_ok : Node.check D_R11111 T3330 [((535/128),(4815/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3330_ok
def T3329 : Node := Node.leaf L3329
theorem T3329_ok : Node.check D_R11111 T3329 [((535/128),(4815/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3329_ok
def T3328 : Node := Node.split 3 T3329 T3330
theorem T3328_ok : Node.check D_R11111 T3328 [((535/128),(4815/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3329_ok T3330_ok
def T3327 : Node := Node.split 0 T3328 T3331
theorem T3327_ok : Node.check D_R11111 T3327 [((535/128),(2675/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3328_ok T3331_ok
def T3326 : Node := Node.leaf L3326
theorem T3326_ok : Node.check D_R11111 T3326 [((535/128),(2675/512)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3326_ok
def T3325 : Node := Node.split 2 T3326 T3327
theorem T3325_ok : Node.check D_R11111 T3325 [((535/128),(2675/512)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3326_ok T3327_ok
def T3324 : Node := Node.split 1 T3325 T3334
theorem T3324_ok : Node.check D_R11111 T3324 [((535/128),(2675/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3325_ok T3334_ok
def T3323 : Node := Node.split 3 T3324 T3347
theorem T3323_ok : Node.check D_R11111 T3323 [((535/128),(2675/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3324_ok T3347_ok
def T3322 : Node := Node.split 0 T3323 T3352
theorem T3322_ok : Node.check D_R11111 T3322 [((535/128),(1605/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3323_ok T3352_ok
def T3321 : Node := Node.split 2 T3322 T3369
theorem T3321_ok : Node.check D_R11111 T3321 [((535/128),(1605/256)),((333/256),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3322_ok T3369_ok
def T3320 : Node := Node.leaf L3320
theorem T3320_ok : Node.check D_R11111 T3320 [((2675/512),(1605/256)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3320_ok
def T3319 : Node := Node.leaf L3319
theorem T3319_ok : Node.check D_R11111 T3319 [((2675/512),(1605/256)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3319_ok
def T3318 : Node := Node.leaf L3318
theorem T3318_ok : Node.check D_R11111 T3318 [((2675/512),(1605/256)),((0),(333/512)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3318_ok
def T3317 : Node := Node.leaf L3317
theorem T3317_ok : Node.check D_R11111 T3317 [((5885/1024),(1605/256)),((0),(333/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3317_ok
def T3316 : Node := Node.leaf L3316
theorem T3316_ok : Node.check D_R11111 T3316 [((5885/1024),(1605/256)),((0),(333/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3316_ok
def T3315 : Node := Node.split 3 T3316 T3317
theorem T3315_ok : Node.check D_R11111 T3315 [((5885/1024),(1605/256)),((0),(333/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3316_ok T3317_ok
def T3314 : Node := Node.leaf L3314
theorem T3314_ok : Node.check D_R11111 T3314 [((2675/512),(5885/1024)),((0),(333/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3314_ok
def T3313 : Node := Node.leaf L3313
theorem T3313_ok : Node.check D_R11111 T3313 [((2675/512),(5885/1024)),((0),(333/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3313_ok
def T3312 : Node := Node.split 3 T3313 T3314
theorem T3312_ok : Node.check D_R11111 T3312 [((2675/512),(5885/1024)),((0),(333/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3313_ok T3314_ok
def T3311 : Node := Node.split 0 T3312 T3315
theorem T3311_ok : Node.check D_R11111 T3311 [((2675/512),(1605/256)),((0),(333/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3312_ok T3315_ok
def T3310 : Node := Node.split 2 T3311 T3318
theorem T3310_ok : Node.check D_R11111 T3310 [((2675/512),(1605/256)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3311_ok T3318_ok
def T3309 : Node := Node.split 1 T3310 T3319
theorem T3309_ok : Node.check D_R11111 T3309 [((2675/512),(1605/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3310_ok T3319_ok
def T3308 : Node := Node.split 3 T3309 T3320
theorem T3308_ok : Node.check D_R11111 T3308 [((2675/512),(1605/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3309_ok T3320_ok
def T3307 : Node := Node.leaf L3307
theorem T3307_ok : Node.check D_R11111 T3307 [((535/128),(2675/512)),((333/512),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3307_ok
def T3306 : Node := Node.leaf L3306
theorem T3306_ok : Node.check D_R11111 T3306 [((535/128),(2675/512)),((0),(333/512)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3306_ok
def T3305 : Node := Node.split 1 T3306 T3307
theorem T3305_ok : Node.check D_R11111 T3305 [((535/128),(2675/512)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3306_ok T3307_ok
def T3304 : Node := Node.leaf L3304
theorem T3304_ok : Node.check D_R11111 T3304 [((535/128),(2675/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3304_ok
def T3303 : Node := Node.leaf L3303
theorem T3303_ok : Node.check D_R11111 T3303 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3303_ok
def T3302 : Node := Node.leaf L3302
theorem T3302_ok : Node.check D_R11111 T3302 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3302_ok
def T3301 : Node := Node.split 3 T3302 T3303
theorem T3301_ok : Node.check D_R11111 T3301 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3302_ok T3303_ok
def T3300 : Node := Node.leaf L3300
theorem T3300_ok : Node.check D_R11111 T3300 [((535/128),(4815/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3300_ok
def T3299 : Node := Node.leaf L3299
theorem T3299_ok : Node.check D_R11111 T3299 [((535/128),(4815/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3299_ok
def T3298 : Node := Node.split 3 T3299 T3300
theorem T3298_ok : Node.check D_R11111 T3298 [((535/128),(4815/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3299_ok T3300_ok
def T3297 : Node := Node.split 0 T3298 T3301
theorem T3297_ok : Node.check D_R11111 T3297 [((535/128),(2675/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3298_ok T3301_ok
def T3296 : Node := Node.split 2 T3297 T3304
theorem T3296_ok : Node.check D_R11111 T3296 [((535/128),(2675/512)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3297_ok T3304_ok
def T3295 : Node := Node.leaf L3295
theorem T3295_ok : Node.check D_R11111 T3295 [((535/128),(2675/512)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3295_ok
def T3294 : Node := Node.split 1 T3295 T3296
theorem T3294_ok : Node.check D_R11111 T3294 [((535/128),(2675/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3295_ok T3296_ok
def T3293 : Node := Node.split 3 T3294 T3305
theorem T3293_ok : Node.check D_R11111 T3293 [((535/128),(2675/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3294_ok T3305_ok
def T3292 : Node := Node.split 0 T3293 T3308
theorem T3292_ok : Node.check D_R11111 T3292 [((535/128),(1605/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3293_ok T3308_ok
def T3291 : Node := Node.leaf L3291
theorem T3291_ok : Node.check D_R11111 T3291 [((2675/512),(1605/256)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3291_ok
def T3290 : Node := Node.leaf L3290
theorem T3290_ok : Node.check D_R11111 T3290 [((2675/512),(1605/256)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3290_ok
def T3289 : Node := Node.split 2 T3290 T3291
theorem T3289_ok : Node.check D_R11111 T3289 [((2675/512),(1605/256)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3290_ok T3291_ok
def T3288 : Node := Node.leaf L3288
theorem T3288_ok : Node.check D_R11111 T3288 [((2675/512),(1605/256)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3288_ok
def T3287 : Node := Node.split 1 T3288 T3289
theorem T3287_ok : Node.check D_R11111 T3287 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3288_ok T3289_ok
def T3286 : Node := Node.leaf L3286
theorem T3286_ok : Node.check D_R11111 T3286 [((5885/1024),(1605/256)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3286_ok
def T3285 : Node := Node.leaf L3285
theorem T3285_ok : Node.check D_R11111 T3285 [((5885/1024),(1605/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3285_ok
def T3284 : Node := Node.split 3 T3285 T3286
theorem T3284_ok : Node.check D_R11111 T3284 [((5885/1024),(1605/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3285_ok T3286_ok
def T3283 : Node := Node.leaf L3283
theorem T3283_ok : Node.check D_R11111 T3283 [((2675/512),(5885/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3283_ok
def T3282 : Node := Node.leaf L3282
theorem T3282_ok : Node.check D_R11111 T3282 [((2675/512),(5885/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3282_ok
def T3281 : Node := Node.split 3 T3282 T3283
theorem T3281_ok : Node.check D_R11111 T3281 [((2675/512),(5885/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3282_ok T3283_ok
def T3280 : Node := Node.split 0 T3281 T3284
theorem T3280_ok : Node.check D_R11111 T3280 [((2675/512),(1605/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3281_ok T3284_ok
def T3279 : Node := Node.leaf L3279
theorem T3279_ok : Node.check D_R11111 T3279 [((2675/512),(1605/256)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3279_ok
def T3278 : Node := Node.split 2 T3279 T3280
theorem T3278_ok : Node.check D_R11111 T3278 [((2675/512),(1605/256)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3279_ok T3280_ok
def T3277 : Node := Node.leaf L3277
theorem T3277_ok : Node.check D_R11111 T3277 [((2675/512),(1605/256)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3277_ok
def T3276 : Node := Node.split 1 T3277 T3278
theorem T3276_ok : Node.check D_R11111 T3276 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3277_ok T3278_ok
def T3275 : Node := Node.split 3 T3276 T3287
theorem T3275_ok : Node.check D_R11111 T3275 [((2675/512),(1605/256)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3276_ok T3287_ok
def T3274 : Node := Node.leaf L3274
theorem T3274_ok : Node.check D_R11111 T3274 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3274_ok
def T3273 : Node := Node.leaf L3273
theorem T3273_ok : Node.check D_R11111 T3273 [((535/128),(4815/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3273_ok
def T3272 : Node := Node.split 0 T3273 T3274
theorem T3272_ok : Node.check D_R11111 T3272 [((535/128),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3273_ok T3274_ok
def T3271 : Node := Node.leaf L3271
theorem T3271_ok : Node.check D_R11111 T3271 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3271_ok
def T3270 : Node := Node.split 2 T3271 T3272
theorem T3270_ok : Node.check D_R11111 T3270 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3271_ok T3272_ok
def T3269 : Node := Node.leaf L3269
theorem T3269_ok : Node.check D_R11111 T3269 [((535/128),(2675/512)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3269_ok
def T3268 : Node := Node.split 1 T3269 T3270
theorem T3268_ok : Node.check D_R11111 T3268 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3269_ok T3270_ok
def T3267 : Node := Node.leaf L3267
theorem T3267_ok : Node.check D_R11111 T3267 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3267_ok
def T3266 : Node := Node.leaf L3266
theorem T3266_ok : Node.check D_R11111 T3266 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3266_ok
def T3265 : Node := Node.split 3 T3266 T3267
theorem T3265_ok : Node.check D_R11111 T3265 [((4815/1024),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3266_ok T3267_ok
def T3264 : Node := Node.leaf L3264
theorem T3264_ok : Node.check D_R11111 T3264 [((535/128),(4815/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3264_ok
def T3263 : Node := Node.leaf L3263
theorem T3263_ok : Node.check D_R11111 T3263 [((535/128),(4815/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3263_ok
def T3262 : Node := Node.split 3 T3263 T3264
theorem T3262_ok : Node.check D_R11111 T3262 [((535/128),(4815/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3263_ok T3264_ok
def T3261 : Node := Node.split 0 T3262 T3265
theorem T3261_ok : Node.check D_R11111 T3261 [((535/128),(2675/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3262_ok T3265_ok
def T3260 : Node := Node.leaf L3260
theorem T3260_ok : Node.check D_R11111 T3260 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3260_ok
def T3259 : Node := Node.split 2 T3260 T3261
theorem T3259_ok : Node.check D_R11111 T3259 [((535/128),(2675/512)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3260_ok T3261_ok
def T3258 : Node := Node.leaf L3258
theorem T3258_ok : Node.check D_R11111 T3258 [((535/128),(2675/512)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3258_ok
def T3257 : Node := Node.split 1 T3258 T3259
theorem T3257_ok : Node.check D_R11111 T3257 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3258_ok T3259_ok
def T3256 : Node := Node.split 3 T3257 T3268
theorem T3256_ok : Node.check D_R11111 T3256 [((535/128),(2675/512)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3257_ok T3268_ok
def T3255 : Node := Node.split 0 T3256 T3275
theorem T3255_ok : Node.check D_R11111 T3255 [((535/128),(1605/256)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3256_ok T3275_ok
def T3254 : Node := Node.split 2 T3255 T3292
theorem T3254_ok : Node.check D_R11111 T3254 [((535/128),(1605/256)),((0),(333/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3255_ok T3292_ok
def T3253 : Node := Node.split 1 T3254 T3321
theorem T3253_ok : Node.check D_R11111 T3253 [((535/128),(1605/256)),((0),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3254_ok T3321_ok
def T3252 : Node := Node.split 3 T3253 T3370
theorem T3252_ok : Node.check D_R11111 T3252 [((535/128),(1605/256)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3253_ok T3370_ok
def T3251 : Node := Node.split 0 T3252 T3393
theorem T3251_ok : Node.check D_R11111 T3251 [((535/128),(535/64)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3252_ok T3393_ok
def T3250 : Node := Node.split 2 T3251 T3446
theorem T3250_ok : Node.check D_R11111 T3250 [((535/128),(535/64)),((0),(333/128)),((0),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3251_ok T3446_ok
def T3249 : Node := Node.split 1 T3250 T3447
theorem T3249_ok : Node.check D_R11111 T3249 [((535/128),(535/64)),((0),(333/64)),((0),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3250_ok T3447_ok
def T3248 : Node := Node.split 3 T3249 T3448
theorem T3248_ok : Node.check D_R11111 T3248 [((535/128),(535/64)),((0),(333/64)),((0),(333/64)),((0),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3249_ok T3448_ok
def T3247 : Node := Node.leaf L3247
theorem T3247_ok : Node.check D_R11111 T3247 [((0),(535/128)),((333/128),(333/64)),((0),(333/64)),((535/128),(535/64))] = true := Node.check_leaf_of _ _ _ L3247_ok
def T3246 : Node := Node.leaf L3246
theorem T3246_ok : Node.check D_R11111 T3246 [((0),(535/128)),((0),(333/128)),((333/128),(333/64)),((535/128),(535/64))] = true := Node.check_leaf_of _ _ _ L3246_ok
def T3245 : Node := Node.leaf L3245
theorem T3245_ok : Node.check D_R11111 T3245 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((1605/256),(535/64))] = true := Node.check_leaf_of _ _ _ L3245_ok
def T3244 : Node := Node.leaf L3244
theorem T3244_ok : Node.check D_R11111 T3244 [((535/256),(535/128)),((333/256),(333/128)),((0),(333/128)),((535/128),(1605/256))] = true := Node.check_leaf_of _ _ _ L3244_ok
def T3243 : Node := Node.leaf L3243
theorem T3243_ok : Node.check D_R11111 T3243 [((535/256),(535/128)),((0),(333/256)),((333/256),(333/128)),((535/128),(1605/256))] = true := Node.check_leaf_of _ _ _ L3243_ok
def T3242 : Node := Node.leaf L3242
theorem T3242_ok : Node.check D_R11111 T3242 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3242_ok
def T3241 : Node := Node.leaf L3241
theorem T3241_ok : Node.check D_R11111 T3241 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3241_ok
def T3240 : Node := Node.leaf L3240
theorem T3240_ok : Node.check D_R11111 T3240 [((1605/512),(535/128)),((0),(333/512)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3240_ok
def T3239 : Node := Node.leaf L3239
theorem T3239_ok : Node.check D_R11111 T3239 [((1605/512),(535/128)),((0),(333/512)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3239_ok
def T3238 : Node := Node.split 2 T3239 T3240
theorem T3238_ok : Node.check D_R11111 T3238 [((1605/512),(535/128)),((0),(333/512)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3239_ok T3240_ok
def T3237 : Node := Node.split 1 T3238 T3241
theorem T3237_ok : Node.check D_R11111 T3237 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3238_ok T3241_ok
def T3236 : Node := Node.split 3 T3237 T3242
theorem T3236_ok : Node.check D_R11111 T3236 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3237_ok T3242_ok
def T3235 : Node := Node.leaf L3235
theorem T3235_ok : Node.check D_R11111 T3235 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3235_ok
def T3234 : Node := Node.leaf L3234
theorem T3234_ok : Node.check D_R11111 T3234 [((535/256),(1605/512)),((0),(333/512)),((333/512),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3234_ok
def T3233 : Node := Node.leaf L3233
theorem T3233_ok : Node.check D_R11111 T3233 [((535/256),(1605/512)),((0),(333/512)),((0),(333/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3233_ok
def T3232 : Node := Node.split 2 T3233 T3234
theorem T3232_ok : Node.check D_R11111 T3232 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3233_ok T3234_ok
def T3231 : Node := Node.split 1 T3232 T3235
theorem T3231_ok : Node.check D_R11111 T3231 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3232_ok T3235_ok
def T3230 : Node := Node.leaf L3230
theorem T3230_ok : Node.check D_R11111 T3230 [((535/256),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3230_ok
def T3229 : Node := Node.leaf L3229
theorem T3229_ok : Node.check D_R11111 T3229 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3229_ok
def T3228 : Node := Node.split 2 T3229 T3230
theorem T3228_ok : Node.check D_R11111 T3228 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3229_ok T3230_ok
def T3227 : Node := Node.leaf L3227
theorem T3227_ok : Node.check D_R11111 T3227 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3227_ok
def T3226 : Node := Node.split 1 T3227 T3228
theorem T3226_ok : Node.check D_R11111 T3226 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3227_ok T3228_ok
def T3225 : Node := Node.split 3 T3226 T3231
theorem T3225_ok : Node.check D_R11111 T3225 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3226_ok T3231_ok
def T3224 : Node := Node.split 0 T3225 T3236
theorem T3224_ok : Node.check D_R11111 T3224 [((535/256),(535/128)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3225_ok T3236_ok
def T3223 : Node := Node.split 2 T3224 T3243
theorem T3223_ok : Node.check D_R11111 T3223 [((535/256),(535/128)),((0),(333/256)),((0),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3224_ok T3243_ok
def T3222 : Node := Node.split 1 T3223 T3244
theorem T3222_ok : Node.check D_R11111 T3222 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3223_ok T3244_ok
def T3221 : Node := Node.split 3 T3222 T3245
theorem T3221_ok : Node.check D_R11111 T3221 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((535/128),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3222_ok T3245_ok
def T3220 : Node := Node.leaf L3220
theorem T3220_ok : Node.check D_R11111 T3220 [((0),(535/256)),((333/256),(333/128)),((0),(333/128)),((1605/256),(535/64))] = true := Node.check_leaf_of _ _ _ L3220_ok
def T3219 : Node := Node.leaf L3219
theorem T3219_ok : Node.check D_R11111 T3219 [((0),(535/256)),((0),(333/256)),((333/256),(333/128)),((1605/256),(535/64))] = true := Node.check_leaf_of _ _ _ L3219_ok
def T3218 : Node := Node.leaf L3218
theorem T3218_ok : Node.check D_R11111 T3218 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((3745/512),(535/64))] = true := Node.check_leaf_of _ _ _ L3218_ok
def T3217 : Node := Node.leaf L3217
theorem T3217_ok : Node.check D_R11111 T3217 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3217_ok
def T3216 : Node := Node.leaf L3216
theorem T3216_ok : Node.check D_R11111 T3216 [((535/512),(535/256)),((0),(333/512)),((333/512),(333/256)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3216_ok
def T3215 : Node := Node.leaf L3215
theorem T3215_ok : Node.check D_R11111 T3215 [((535/512),(535/256)),((0),(333/512)),((0),(333/512)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3215_ok
def T3214 : Node := Node.split 2 T3215 T3216
theorem T3214_ok : Node.check D_R11111 T3214 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((1605/256),(3745/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3215_ok T3216_ok
def T3213 : Node := Node.split 1 T3214 T3217
theorem T3213_ok : Node.check D_R11111 T3213 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((1605/256),(3745/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3214_ok T3217_ok
def T3212 : Node := Node.split 3 T3213 T3218
theorem T3212_ok : Node.check D_R11111 T3212 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((1605/256),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3213_ok T3218_ok
def T3211 : Node := Node.leaf L3211
theorem T3211_ok : Node.check D_R11111 T3211 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((3745/512),(535/64))] = true := Node.check_leaf_of _ _ _ L3211_ok
def T3210 : Node := Node.leaf L3210
theorem T3210_ok : Node.check D_R11111 T3210 [((0),(535/512)),((0),(333/512)),((333/512),(333/256)),((3745/512),(535/64))] = true := Node.check_leaf_of _ _ _ L3210_ok
def T3209 : Node := Node.leaf L3209
theorem T3209_ok : Node.check D_R11111 T3209 [((535/1024),(535/512)),((0),(333/512)),((0),(333/512)),((8025/1024),(535/64))] = true := Node.check_leaf_of _ _ _ L3209_ok
def T3208 : Node := Node.leaf L3208
theorem T3208_ok : Node.check D_R11111 T3208 [((535/1024),(535/512)),((333/1024),(333/512)),((0),(333/512)),((3745/512),(8025/1024))] = true := Node.check_leaf_of _ _ _ L3208_ok
def T3207 : Node := Node.leaf L3207
theorem T3207_ok : Node.check D_R11111 T3207 [((535/1024),(535/512)),((0),(333/1024)),((0),(333/512)),((3745/512),(8025/1024))] = true := Node.check_leaf_of _ _ _ L3207_ok
def T3206 : Node := Node.split 1 T3207 T3208
theorem T3206_ok : Node.check D_R11111 T3206 [((535/1024),(535/512)),((0),(333/512)),((0),(333/512)),((3745/512),(8025/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3207_ok T3208_ok
def T3205 : Node := Node.split 3 T3206 T3209
theorem T3205_ok : Node.check D_R11111 T3205 [((535/1024),(535/512)),((0),(333/512)),((0),(333/512)),((3745/512),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3206_ok T3209_ok
def T3204 : Node := Node.leaf L3204
theorem T3204_ok : Node.check D_R11111 T3204 [((0),(535/1024)),((0),(333/512)),((0),(333/512)),((3745/512),(535/64))] = true := Node.check_leaf_of _ _ _ L3204_ok
def T3203 : Node := Node.split 0 T3204 T3205
theorem T3203_ok : Node.check D_R11111 T3203 [((0),(535/512)),((0),(333/512)),((0),(333/512)),((3745/512),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3204_ok T3205_ok
def T3202 : Node := Node.split 2 T3203 T3210
theorem T3202_ok : Node.check D_R11111 T3202 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((3745/512),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3203_ok T3210_ok
def T3201 : Node := Node.split 1 T3202 T3211
theorem T3201_ok : Node.check D_R11111 T3201 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((3745/512),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3202_ok T3211_ok
def T3200 : Node := Node.leaf L3200
theorem T3200_ok : Node.check D_R11111 T3200 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3200_ok
def T3199 : Node := Node.leaf L3199
theorem T3199_ok : Node.check D_R11111 T3199 [((535/1024),(535/512)),((333/512),(333/256)),((0),(333/512)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3199_ok
def T3198 : Node := Node.leaf L3198
theorem T3198_ok : Node.check D_R11111 T3198 [((0),(535/1024)),((333/512),(333/256)),((0),(333/512)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3198_ok
def T3197 : Node := Node.split 0 T3198 T3199
theorem T3197_ok : Node.check D_R11111 T3197 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((1605/256),(3745/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3198_ok T3199_ok
def T3196 : Node := Node.split 2 T3197 T3200
theorem T3196_ok : Node.check D_R11111 T3196 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((1605/256),(3745/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3197_ok T3200_ok
def T3195 : Node := Node.leaf L3195
theorem T3195_ok : Node.check D_R11111 T3195 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((1605/256),(3745/512))] = true := Node.check_leaf_of _ _ _ L3195_ok
def T3194 : Node := Node.split 1 T3195 T3196
theorem T3194_ok : Node.check D_R11111 T3194 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((1605/256),(3745/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3195_ok T3196_ok
def T3193 : Node := Node.split 3 T3194 T3201
theorem T3193_ok : Node.check D_R11111 T3193 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((1605/256),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3194_ok T3201_ok
def T3192 : Node := Node.split 0 T3193 T3212
theorem T3192_ok : Node.check D_R11111 T3192 [((0),(535/256)),((0),(333/256)),((0),(333/256)),((1605/256),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3193_ok T3212_ok
def T3191 : Node := Node.split 2 T3192 T3219
theorem T3191_ok : Node.check D_R11111 T3191 [((0),(535/256)),((0),(333/256)),((0),(333/128)),((1605/256),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3192_ok T3219_ok
def T3190 : Node := Node.split 1 T3191 T3220
theorem T3190_ok : Node.check D_R11111 T3190 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((1605/256),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3191_ok T3220_ok
def T3189 : Node := Node.leaf L3189
theorem T3189_ok : Node.check D_R11111 T3189 [((0),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((535/128),(1605/256))] = true := Node.check_leaf_of _ _ _ L3189_ok
def T3188 : Node := Node.leaf L3188
theorem T3188_ok : Node.check D_R11111 T3188 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3188_ok
def T3187 : Node := Node.leaf L3187
theorem T3187_ok : Node.check D_R11111 T3187 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3187_ok
def T3186 : Node := Node.leaf L3186
theorem T3186_ok : Node.check D_R11111 T3186 [((535/512),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3186_ok
def T3185 : Node := Node.leaf L3185
theorem T3185_ok : Node.check D_R11111 T3185 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3185_ok
def T3184 : Node := Node.split 2 T3185 T3186
theorem T3184_ok : Node.check D_R11111 T3184 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3185_ok T3186_ok
def T3183 : Node := Node.split 1 T3184 T3187
theorem T3183_ok : Node.check D_R11111 T3183 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3184_ok T3187_ok
def T3182 : Node := Node.split 3 T3183 T3188
theorem T3182_ok : Node.check D_R11111 T3182 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3183_ok T3188_ok
def T3181 : Node := Node.leaf L3181
theorem T3181_ok : Node.check D_R11111 T3181 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3181_ok
def T3180 : Node := Node.leaf L3180
theorem T3180_ok : Node.check D_R11111 T3180 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3180_ok
def T3179 : Node := Node.leaf L3179
theorem T3179_ok : Node.check D_R11111 T3179 [((535/1024),(535/512)),((333/256),(999/512)),((0),(333/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3179_ok
def T3178 : Node := Node.leaf L3178
theorem T3178_ok : Node.check D_R11111 T3178 [((0),(535/1024)),((333/256),(999/512)),((0),(333/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3178_ok
def T3177 : Node := Node.split 0 T3178 T3179
theorem T3177_ok : Node.check D_R11111 T3177 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3178_ok T3179_ok
def T3176 : Node := Node.split 2 T3177 T3180
theorem T3176_ok : Node.check D_R11111 T3176 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3177_ok T3180_ok
def T3175 : Node := Node.split 1 T3176 T3181
theorem T3175_ok : Node.check D_R11111 T3175 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3176_ok T3181_ok
def T3174 : Node := Node.leaf L3174
theorem T3174_ok : Node.check D_R11111 T3174 [((0),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3174_ok
def T3173 : Node := Node.leaf L3173
theorem T3173_ok : Node.check D_R11111 T3173 [((535/1024),(535/512)),((999/512),(333/128)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3173_ok
def T3172 : Node := Node.leaf L3172
theorem T3172_ok : Node.check D_R11111 T3172 [((0),(535/1024)),((999/512),(333/128)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3172_ok
def T3171 : Node := Node.split 0 T3172 T3173
theorem T3171_ok : Node.check D_R11111 T3171 [((0),(535/512)),((999/512),(333/128)),((0),(333/512)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3172_ok T3173_ok
def T3170 : Node := Node.split 2 T3171 T3174
theorem T3170_ok : Node.check D_R11111 T3170 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3171_ok T3174_ok
def T3169 : Node := Node.leaf L3169
theorem T3169_ok : Node.check D_R11111 T3169 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3169_ok
def T3168 : Node := Node.leaf L3168
theorem T3168_ok : Node.check D_R11111 T3168 [((0),(535/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3168_ok
def T3167 : Node := Node.split 0 T3168 T3169
theorem T3167_ok : Node.check D_R11111 T3167 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3168_ok T3169_ok
def T3166 : Node := Node.leaf L3166
theorem T3166_ok : Node.check D_R11111 T3166 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3166_ok
def T3165 : Node := Node.split 2 T3166 T3167
theorem T3165_ok : Node.check D_R11111 T3165 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3166_ok T3167_ok
def T3164 : Node := Node.split 1 T3165 T3170
theorem T3164_ok : Node.check D_R11111 T3164 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3165_ok T3170_ok
def T3163 : Node := Node.split 3 T3164 T3175
theorem T3163_ok : Node.check D_R11111 T3163 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3164_ok T3175_ok
def T3162 : Node := Node.split 0 T3163 T3182
theorem T3162_ok : Node.check D_R11111 T3162 [((0),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3163_ok T3182_ok
def T3161 : Node := Node.split 2 T3162 T3189
theorem T3161_ok : Node.check D_R11111 T3161 [((0),(535/256)),((333/256),(333/128)),((0),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3162_ok T3189_ok
def T3160 : Node := Node.leaf L3160
theorem T3160_ok : Node.check D_R11111 T3160 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3160_ok
def T3159 : Node := Node.leaf L3159
theorem T3159_ok : Node.check D_R11111 T3159 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(333/128)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3159_ok
def T3158 : Node := Node.leaf L3158
theorem T3158_ok : Node.check D_R11111 T3158 [((535/512),(535/256)),((0),(333/512)),((333/256),(333/128)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3158_ok
def T3157 : Node := Node.split 1 T3158 T3159
theorem T3157_ok : Node.check D_R11111 T3157 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3158_ok T3159_ok
def T3156 : Node := Node.split 3 T3157 T3160
theorem T3156_ok : Node.check D_R11111 T3156 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3157_ok T3160_ok
def T3155 : Node := Node.leaf L3155
theorem T3155_ok : Node.check D_R11111 T3155 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3155_ok
def T3154 : Node := Node.leaf L3154
theorem T3154_ok : Node.check D_R11111 T3154 [((0),(535/512)),((0),(333/512)),((999/512),(333/128)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3154_ok
def T3153 : Node := Node.leaf L3153
theorem T3153_ok : Node.check D_R11111 T3153 [((535/1024),(535/512)),((0),(333/512)),((333/256),(999/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3153_ok
def T3152 : Node := Node.leaf L3152
theorem T3152_ok : Node.check D_R11111 T3152 [((0),(535/1024)),((0),(333/512)),((333/256),(999/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3152_ok
def T3151 : Node := Node.split 0 T3152 T3153
theorem T3151_ok : Node.check D_R11111 T3151 [((0),(535/512)),((0),(333/512)),((333/256),(999/512)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3152_ok T3153_ok
def T3150 : Node := Node.split 2 T3151 T3154
theorem T3150_ok : Node.check D_R11111 T3150 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3151_ok T3154_ok
def T3149 : Node := Node.split 1 T3150 T3155
theorem T3149_ok : Node.check D_R11111 T3149 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3150_ok T3155_ok
def T3148 : Node := Node.leaf L3148
theorem T3148_ok : Node.check D_R11111 T3148 [((0),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3148_ok
def T3147 : Node := Node.leaf L3147
theorem T3147_ok : Node.check D_R11111 T3147 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3147_ok
def T3146 : Node := Node.leaf L3146
theorem T3146_ok : Node.check D_R11111 T3146 [((0),(535/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3146_ok
def T3145 : Node := Node.split 0 T3146 T3147
theorem T3145_ok : Node.check D_R11111 T3145 [((0),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3146_ok T3147_ok
def T3144 : Node := Node.split 2 T3145 T3148
theorem T3144_ok : Node.check D_R11111 T3144 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3145_ok T3148_ok
def T3143 : Node := Node.leaf L3143
theorem T3143_ok : Node.check D_R11111 T3143 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3143_ok
def T3142 : Node := Node.split 1 T3143 T3144
theorem T3142_ok : Node.check D_R11111 T3142 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3143_ok T3144_ok
def T3141 : Node := Node.split 3 T3142 T3149
theorem T3141_ok : Node.check D_R11111 T3141 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3142_ok T3149_ok
def T3140 : Node := Node.split 0 T3141 T3156
theorem T3140_ok : Node.check D_R11111 T3140 [((0),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3141_ok T3156_ok
def T3139 : Node := Node.leaf L3139
theorem T3139_ok : Node.check D_R11111 T3139 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3139_ok
def T3138 : Node := Node.leaf L3138
theorem T3138_ok : Node.check D_R11111 T3138 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3138_ok
def T3137 : Node := Node.split 2 T3138 T3139
theorem T3137_ok : Node.check D_R11111 T3137 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3138_ok T3139_ok
def T3136 : Node := Node.leaf L3136
theorem T3136_ok : Node.check D_R11111 T3136 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3136_ok
def T3135 : Node := Node.split 1 T3136 T3137
theorem T3135_ok : Node.check D_R11111 T3135 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3136_ok T3137_ok
def T3134 : Node := Node.leaf L3134
theorem T3134_ok : Node.check D_R11111 T3134 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3134_ok
def T3133 : Node := Node.leaf L3133
theorem T3133_ok : Node.check D_R11111 T3133 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((4815/1024),(2675/512))] = true := Node.check_leaf_of _ _ _ L3133_ok
def T3132 : Node := Node.leaf L3132
theorem T3132_ok : Node.check D_R11111 T3132 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(4815/1024))] = true := Node.check_leaf_of _ _ _ L3132_ok
def T3131 : Node := Node.split 3 T3132 T3133
theorem T3131_ok : Node.check D_R11111 T3131 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3132_ok T3133_ok
def T3130 : Node := Node.split 0 T3131 T3134
theorem T3130_ok : Node.check D_R11111 T3130 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3131_ok T3134_ok
def T3129 : Node := Node.leaf L3129
theorem T3129_ok : Node.check D_R11111 T3129 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3129_ok
def T3128 : Node := Node.split 2 T3129 T3130
theorem T3128_ok : Node.check D_R11111 T3128 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3129_ok T3130_ok
def T3127 : Node := Node.leaf L3127
theorem T3127_ok : Node.check D_R11111 T3127 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3127_ok
def T3126 : Node := Node.split 1 T3127 T3128
theorem T3126_ok : Node.check D_R11111 T3126 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3127_ok T3128_ok
def T3125 : Node := Node.split 3 T3126 T3135
theorem T3125_ok : Node.check D_R11111 T3125 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3126_ok T3135_ok
def T3124 : Node := Node.leaf L3124
theorem T3124_ok : Node.check D_R11111 T3124 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3124_ok
def T3123 : Node := Node.leaf L3123
theorem T3123_ok : Node.check D_R11111 T3123 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3123_ok
def T3122 : Node := Node.split 0 T3123 T3124
theorem T3122_ok : Node.check D_R11111 T3122 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3123_ok T3124_ok
def T3121 : Node := Node.leaf L3121
theorem T3121_ok : Node.check D_R11111 T3121 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3121_ok
def T3120 : Node := Node.split 2 T3121 T3122
theorem T3120_ok : Node.check D_R11111 T3120 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3121_ok T3122_ok
def T3119 : Node := Node.leaf L3119
theorem T3119_ok : Node.check D_R11111 T3119 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((2675/512),(1605/256))] = true := Node.check_leaf_of _ _ _ L3119_ok
def T3118 : Node := Node.split 1 T3119 T3120
theorem T3118_ok : Node.check D_R11111 T3118 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((2675/512),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3119_ok T3120_ok
def T3117 : Node := Node.leaf L3117
theorem T3117_ok : Node.check D_R11111 T3117 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3117_ok
def T3116 : Node := Node.leaf L3116
theorem T3116_ok : Node.check D_R11111 T3116 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3116_ok
def T3115 : Node := Node.split 0 T3116 T3117
theorem T3115_ok : Node.check D_R11111 T3115 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3116_ok T3117_ok
def T3114 : Node := Node.leaf L3114
theorem T3114_ok : Node.check D_R11111 T3114 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3114_ok
def T3113 : Node := Node.split 2 T3114 T3115
theorem T3113_ok : Node.check D_R11111 T3113 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3114_ok T3115_ok
def T3112 : Node := Node.leaf L3112
theorem T3112_ok : Node.check D_R11111 T3112 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((535/128),(2675/512))] = true := Node.check_leaf_of _ _ _ L3112_ok
def T3111 : Node := Node.split 1 T3112 T3113
theorem T3111_ok : Node.check D_R11111 T3111 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((535/128),(2675/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3112_ok T3113_ok
def T3110 : Node := Node.split 3 T3111 T3118
theorem T3110_ok : Node.check D_R11111 T3110 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3111_ok T3118_ok
def T3109 : Node := Node.split 0 T3110 T3125
theorem T3109_ok : Node.check D_R11111 T3109 [((0),(535/256)),((0),(333/256)),((0),(333/256)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3110_ok T3125_ok
def T3108 : Node := Node.split 2 T3109 T3140
theorem T3108_ok : Node.check D_R11111 T3108 [((0),(535/256)),((0),(333/256)),((0),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3109_ok T3140_ok
def T3107 : Node := Node.split 1 T3108 T3161
theorem T3107_ok : Node.check D_R11111 T3107 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((535/128),(1605/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3108_ok T3161_ok
def T3106 : Node := Node.split 3 T3107 T3190
theorem T3106_ok : Node.check D_R11111 T3106 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((535/128),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3107_ok T3190_ok
def T3105 : Node := Node.split 0 T3106 T3221
theorem T3105_ok : Node.check D_R11111 T3105 [((0),(535/128)),((0),(333/128)),((0),(333/128)),((535/128),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3106_ok T3221_ok
def T3104 : Node := Node.split 2 T3105 T3246
theorem T3104_ok : Node.check D_R11111 T3104 [((0),(535/128)),((0),(333/128)),((0),(333/64)),((535/128),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3105_ok T3246_ok
def T3103 : Node := Node.split 1 T3104 T3247
theorem T3103_ok : Node.check D_R11111 T3103 [((0),(535/128)),((0),(333/64)),((0),(333/64)),((535/128),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3104_ok T3247_ok
def T3102 : Node := Node.leaf L3102
theorem T3102_ok : Node.check D_R11111 T3102 [((0),(535/128)),((333/128),(333/64)),((333/128),(333/64)),((0),(535/128))] = true := Node.check_leaf_of _ _ _ L3102_ok
def T3101 : Node := Node.leaf L3101
theorem T3101_ok : Node.check D_R11111 T3101 [((535/256),(535/128)),((333/128),(333/64)),((0),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3101_ok
def T3100 : Node := Node.leaf L3100
theorem T3100_ok : Node.check D_R11111 T3100 [((535/256),(535/128)),((999/256),(333/64)),((0),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3100_ok
def T3099 : Node := Node.leaf L3099
theorem T3099_ok : Node.check D_R11111 T3099 [((535/256),(535/128)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3099_ok
def T3098 : Node := Node.leaf L3098
theorem T3098_ok : Node.check D_R11111 T3098 [((1605/512),(535/128)),((333/128),(999/256)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3098_ok
def T3097 : Node := Node.leaf L3097
theorem T3097_ok : Node.check D_R11111 T3097 [((1605/512),(535/128)),((1665/512),(999/256)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3097_ok
def T3096 : Node := Node.leaf L3096
theorem T3096_ok : Node.check D_R11111 T3096 [((1605/512),(535/128)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3096_ok
def T3095 : Node := Node.leaf L3095
theorem T3095_ok : Node.check D_R11111 T3095 [((3745/1024),(535/128)),((333/128),(1665/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3095_ok
def T3094 : Node := Node.leaf L3094
theorem T3094_ok : Node.check D_R11111 T3094 [((3745/1024),(535/128)),((2997/1024),(1665/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3094_ok
def T3093 : Node := Node.leaf L3093
theorem T3093_ok : Node.check D_R11111 T3093 [((3745/1024),(535/128)),((333/128),(2997/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3093_ok
def T3092 : Node := Node.leaf L3092
theorem T3092_ok : Node.check D_R11111 T3092 [((3745/1024),(535/128)),((333/128),(2997/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3092_ok
def T3091 : Node := Node.split 2 T3092 T3093
theorem T3091_ok : Node.check D_R11111 T3091 [((3745/1024),(535/128)),((333/128),(2997/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3092_ok T3093_ok
def T3090 : Node := Node.split 1 T3091 T3094
theorem T3090_ok : Node.check D_R11111 T3090 [((3745/1024),(535/128)),((333/128),(1665/512)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3091_ok T3094_ok
def T3089 : Node := Node.split 3 T3090 T3095
theorem T3089_ok : Node.check D_R11111 T3089 [((3745/1024),(535/128)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3090_ok T3095_ok
def T3088 : Node := Node.leaf L3088
theorem T3088_ok : Node.check D_R11111 T3088 [((1605/512),(3745/1024)),((333/128),(1665/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3088_ok
def T3087 : Node := Node.leaf L3087
theorem T3087_ok : Node.check D_R11111 T3087 [((1605/512),(3745/1024)),((333/128),(1665/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3087_ok
def T3086 : Node := Node.split 3 T3087 T3088
theorem T3086_ok : Node.check D_R11111 T3086 [((1605/512),(3745/1024)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3087_ok T3088_ok
def T3085 : Node := Node.split 0 T3086 T3089
theorem T3085_ok : Node.check D_R11111 T3085 [((1605/512),(535/128)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3086_ok T3089_ok
def T3084 : Node := Node.split 2 T3085 T3096
theorem T3084_ok : Node.check D_R11111 T3084 [((1605/512),(535/128)),((333/128),(1665/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3085_ok T3096_ok
def T3083 : Node := Node.split 1 T3084 T3097
theorem T3083_ok : Node.check D_R11111 T3083 [((1605/512),(535/128)),((333/128),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3084_ok T3097_ok
def T3082 : Node := Node.split 3 T3083 T3098
theorem T3082_ok : Node.check D_R11111 T3082 [((1605/512),(535/128)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3083_ok T3098_ok
def T3081 : Node := Node.leaf L3081
theorem T3081_ok : Node.check D_R11111 T3081 [((535/256),(1605/512)),((1665/512),(999/256)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3081_ok
def T3080 : Node := Node.leaf L3080
theorem T3080_ok : Node.check D_R11111 T3080 [((535/256),(1605/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3080_ok
def T3079 : Node := Node.leaf L3079
theorem T3079_ok : Node.check D_R11111 T3079 [((535/256),(1605/512)),((333/128),(1665/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3079_ok
def T3078 : Node := Node.split 2 T3079 T3080
theorem T3078_ok : Node.check D_R11111 T3078 [((535/256),(1605/512)),((333/128),(1665/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3079_ok T3080_ok
def T3077 : Node := Node.split 1 T3078 T3081
theorem T3077_ok : Node.check D_R11111 T3077 [((535/256),(1605/512)),((333/128),(999/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3078_ok T3081_ok
def T3076 : Node := Node.leaf L3076
theorem T3076_ok : Node.check D_R11111 T3076 [((535/256),(1605/512)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3076_ok
def T3075 : Node := Node.leaf L3075
theorem T3075_ok : Node.check D_R11111 T3075 [((2675/1024),(1605/512)),((1665/512),(999/256)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3075_ok
def T3074 : Node := Node.leaf L3074
theorem T3074_ok : Node.check D_R11111 T3074 [((2675/1024),(1605/512)),((3663/1024),(999/256)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3074_ok
def T3073 : Node := Node.leaf L3073
theorem T3073_ok : Node.check D_R11111 T3073 [((2675/1024),(1605/512)),((1665/512),(3663/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3073_ok
def T3072 : Node := Node.leaf L3072
theorem T3072_ok : Node.check D_R11111 T3072 [((2675/1024),(1605/512)),((1665/512),(3663/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3072_ok
def T3071 : Node := Node.split 2 T3072 T3073
theorem T3071_ok : Node.check D_R11111 T3071 [((2675/1024),(1605/512)),((1665/512),(3663/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3072_ok T3073_ok
def T3070 : Node := Node.split 1 T3071 T3074
theorem T3070_ok : Node.check D_R11111 T3070 [((2675/1024),(1605/512)),((1665/512),(999/256)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3071_ok T3074_ok
def T3069 : Node := Node.split 3 T3070 T3075
theorem T3069_ok : Node.check D_R11111 T3069 [((2675/1024),(1605/512)),((1665/512),(999/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3070_ok T3075_ok
def T3068 : Node := Node.leaf L3068
theorem T3068_ok : Node.check D_R11111 T3068 [((535/256),(2675/1024)),((1665/512),(999/256)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3068_ok
def T3067 : Node := Node.leaf L3067
theorem T3067_ok : Node.check D_R11111 T3067 [((535/256),(2675/1024)),((1665/512),(999/256)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3067_ok
def T3066 : Node := Node.split 3 T3067 T3068
theorem T3066_ok : Node.check D_R11111 T3066 [((535/256),(2675/1024)),((1665/512),(999/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3067_ok T3068_ok
def T3065 : Node := Node.split 0 T3066 T3069
theorem T3065_ok : Node.check D_R11111 T3065 [((535/256),(1605/512)),((1665/512),(999/256)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3066_ok T3069_ok
def T3064 : Node := Node.split 2 T3065 T3076
theorem T3064_ok : Node.check D_R11111 T3064 [((535/256),(1605/512)),((1665/512),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3065_ok T3076_ok
def T3063 : Node := Node.leaf L3063
theorem T3063_ok : Node.check D_R11111 T3063 [((2675/1024),(1605/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3063_ok
def T3062 : Node := Node.leaf L3062
theorem T3062_ok : Node.check D_R11111 T3062 [((2675/1024),(1605/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3062_ok
def T3061 : Node := Node.split 3 T3062 T3063
theorem T3061_ok : Node.check D_R11111 T3061 [((2675/1024),(1605/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3062_ok T3063_ok
def T3060 : Node := Node.leaf L3060
theorem T3060_ok : Node.check D_R11111 T3060 [((535/256),(2675/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3060_ok
def T3059 : Node := Node.leaf L3059
theorem T3059_ok : Node.check D_R11111 T3059 [((535/256),(2675/1024)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3059_ok
def T3058 : Node := Node.split 3 T3059 T3060
theorem T3058_ok : Node.check D_R11111 T3058 [((535/256),(2675/1024)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3059_ok T3060_ok
def T3057 : Node := Node.split 0 T3058 T3061
theorem T3057_ok : Node.check D_R11111 T3057 [((535/256),(1605/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3058_ok T3061_ok
def T3056 : Node := Node.leaf L3056
theorem T3056_ok : Node.check D_R11111 T3056 [((535/256),(1605/512)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3056_ok
def T3055 : Node := Node.split 2 T3056 T3057
theorem T3055_ok : Node.check D_R11111 T3055 [((535/256),(1605/512)),((333/128),(1665/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3056_ok T3057_ok
def T3054 : Node := Node.split 1 T3055 T3064
theorem T3054_ok : Node.check D_R11111 T3054 [((535/256),(1605/512)),((333/128),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3055_ok T3064_ok
def T3053 : Node := Node.split 3 T3054 T3077
theorem T3053_ok : Node.check D_R11111 T3053 [((535/256),(1605/512)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3054_ok T3077_ok
def T3052 : Node := Node.split 0 T3053 T3082
theorem T3052_ok : Node.check D_R11111 T3052 [((535/256),(535/128)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3053_ok T3082_ok
def T3051 : Node := Node.split 2 T3052 T3099
theorem T3051_ok : Node.check D_R11111 T3051 [((535/256),(535/128)),((333/128),(999/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3052_ok T3099_ok
def T3050 : Node := Node.split 1 T3051 T3100
theorem T3050_ok : Node.check D_R11111 T3050 [((535/256),(535/128)),((333/128),(333/64)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3051_ok T3100_ok
def T3049 : Node := Node.split 3 T3050 T3101
theorem T3049_ok : Node.check D_R11111 T3049 [((535/256),(535/128)),((333/128),(333/64)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3050_ok T3101_ok
def T3048 : Node := Node.leaf L3048
theorem T3048_ok : Node.check D_R11111 T3048 [((0),(535/256)),((999/256),(333/64)),((0),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3048_ok
def T3047 : Node := Node.leaf L3047
theorem T3047_ok : Node.check D_R11111 T3047 [((0),(535/256)),((333/128),(999/256)),((333/256),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L3047_ok
def T3046 : Node := Node.leaf L3046
theorem T3046_ok : Node.check D_R11111 T3046 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3046_ok
def T3045 : Node := Node.leaf L3045
theorem T3045_ok : Node.check D_R11111 T3045 [((535/512),(535/256)),((1665/512),(999/256)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3045_ok
def T3044 : Node := Node.leaf L3044
theorem T3044_ok : Node.check D_R11111 T3044 [((535/512),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3044_ok
def T3043 : Node := Node.leaf L3043
theorem T3043_ok : Node.check D_R11111 T3043 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3043_ok
def T3042 : Node := Node.split 2 T3043 T3044
theorem T3042_ok : Node.check D_R11111 T3042 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3043_ok T3044_ok
def T3041 : Node := Node.split 1 T3042 T3045
theorem T3041_ok : Node.check D_R11111 T3041 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3042_ok T3045_ok
def T3040 : Node := Node.split 3 T3041 T3046
theorem T3040_ok : Node.check D_R11111 T3040 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3041_ok T3046_ok
def T3039 : Node := Node.leaf L3039
theorem T3039_ok : Node.check D_R11111 T3039 [((0),(535/512)),((1665/512),(999/256)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3039_ok
def T3038 : Node := Node.leaf L3038
theorem T3038_ok : Node.check D_R11111 T3038 [((0),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3038_ok
def T3037 : Node := Node.leaf L3037
theorem T3037_ok : Node.check D_R11111 T3037 [((535/1024),(535/512)),((333/128),(1665/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3037_ok
def T3036 : Node := Node.leaf L3036
theorem T3036_ok : Node.check D_R11111 T3036 [((0),(535/1024)),((333/128),(1665/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L3036_ok
def T3035 : Node := Node.split 0 T3036 T3037
theorem T3035_ok : Node.check D_R11111 T3035 [((0),(535/512)),((333/128),(1665/512)),((0),(333/512)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3036_ok T3037_ok
def T3034 : Node := Node.split 2 T3035 T3038
theorem T3034_ok : Node.check D_R11111 T3034 [((0),(535/512)),((333/128),(1665/512)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3035_ok T3038_ok
def T3033 : Node := Node.split 1 T3034 T3039
theorem T3033_ok : Node.check D_R11111 T3033 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3034_ok T3039_ok
def T3032 : Node := Node.leaf L3032
theorem T3032_ok : Node.check D_R11111 T3032 [((0),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3032_ok
def T3031 : Node := Node.leaf L3031
theorem T3031_ok : Node.check D_R11111 T3031 [((535/1024),(535/512)),((1665/512),(999/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3031_ok
def T3030 : Node := Node.leaf L3030
theorem T3030_ok : Node.check D_R11111 T3030 [((0),(535/1024)),((1665/512),(999/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3030_ok
def T3029 : Node := Node.split 0 T3030 T3031
theorem T3029_ok : Node.check D_R11111 T3029 [((0),(535/512)),((1665/512),(999/256)),((0),(333/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3030_ok T3031_ok
def T3028 : Node := Node.split 2 T3029 T3032
theorem T3028_ok : Node.check D_R11111 T3028 [((0),(535/512)),((1665/512),(999/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3029_ok T3032_ok
def T3027 : Node := Node.leaf L3027
theorem T3027_ok : Node.check D_R11111 T3027 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3027_ok
def T3026 : Node := Node.leaf L3026
theorem T3026_ok : Node.check D_R11111 T3026 [((0),(535/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3026_ok
def T3025 : Node := Node.split 0 T3026 T3027
theorem T3025_ok : Node.check D_R11111 T3025 [((0),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3026_ok T3027_ok
def T3024 : Node := Node.leaf L3024
theorem T3024_ok : Node.check D_R11111 T3024 [((0),(535/512)),((333/128),(1665/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L3024_ok
def T3023 : Node := Node.split 2 T3024 T3025
theorem T3023_ok : Node.check D_R11111 T3023 [((0),(535/512)),((333/128),(1665/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3024_ok T3025_ok
def T3022 : Node := Node.split 1 T3023 T3028
theorem T3022_ok : Node.check D_R11111 T3022 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3023_ok T3028_ok
def T3021 : Node := Node.split 3 T3022 T3033
theorem T3021_ok : Node.check D_R11111 T3021 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3022_ok T3033_ok
def T3020 : Node := Node.split 0 T3021 T3040
theorem T3020_ok : Node.check D_R11111 T3020 [((0),(535/256)),((333/128),(999/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3021_ok T3040_ok
def T3019 : Node := Node.split 2 T3020 T3047
theorem T3019_ok : Node.check D_R11111 T3019 [((0),(535/256)),((333/128),(999/256)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3020_ok T3047_ok
def T3018 : Node := Node.split 1 T3019 T3048
theorem T3018_ok : Node.check D_R11111 T3018 [((0),(535/256)),((333/128),(333/64)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3019_ok T3048_ok
def T3017 : Node := Node.leaf L3017
theorem T3017_ok : Node.check D_R11111 T3017 [((0),(535/256)),((999/256),(333/64)),((333/256),(333/128)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L3017_ok
def T3016 : Node := Node.leaf L3016
theorem T3016_ok : Node.check D_R11111 T3016 [((535/512),(535/256)),((999/256),(333/64)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L3016_ok
def T3015 : Node := Node.leaf L3015
theorem T3015_ok : Node.check D_R11111 T3015 [((535/512),(535/256)),((2331/512),(333/64)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3015_ok
def T3014 : Node := Node.leaf L3014
theorem T3014_ok : Node.check D_R11111 T3014 [((535/512),(535/256)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L3014_ok
def T3013 : Node := Node.leaf L3013
theorem T3013_ok : Node.check D_R11111 T3013 [((1605/1024),(535/256)),((999/256),(2331/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3013_ok
def T3012 : Node := Node.leaf L3012
theorem T3012_ok : Node.check D_R11111 T3012 [((1605/1024),(535/256)),((4329/1024),(2331/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3012_ok
def T3011 : Node := Node.leaf L3011
theorem T3011_ok : Node.check D_R11111 T3011 [((1605/1024),(535/256)),((999/256),(4329/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3011_ok
def T3010 : Node := Node.leaf L3010
theorem T3010_ok : Node.check D_R11111 T3010 [((1605/1024),(535/256)),((999/256),(4329/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3010_ok
def T3009 : Node := Node.split 2 T3010 T3011
theorem T3009_ok : Node.check D_R11111 T3009 [((1605/1024),(535/256)),((999/256),(4329/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3010_ok T3011_ok
def T3008 : Node := Node.split 1 T3009 T3012
theorem T3008_ok : Node.check D_R11111 T3008 [((1605/1024),(535/256)),((999/256),(2331/512)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3009_ok T3012_ok
def T3007 : Node := Node.split 3 T3008 T3013
theorem T3007_ok : Node.check D_R11111 T3007 [((1605/1024),(535/256)),((999/256),(2331/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3008_ok T3013_ok
def T3006 : Node := Node.leaf L3006
theorem T3006_ok : Node.check D_R11111 T3006 [((535/512),(1605/1024)),((999/256),(2331/512)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L3006_ok
def T3005 : Node := Node.leaf L3005
theorem T3005_ok : Node.check D_R11111 T3005 [((535/512),(1605/1024)),((999/256),(2331/512)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L3005_ok
def T3004 : Node := Node.split 3 T3005 T3006
theorem T3004_ok : Node.check D_R11111 T3004 [((535/512),(1605/1024)),((999/256),(2331/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3005_ok T3006_ok
def T3003 : Node := Node.split 0 T3004 T3007
theorem T3003_ok : Node.check D_R11111 T3003 [((535/512),(535/256)),((999/256),(2331/512)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3004_ok T3007_ok
def T3002 : Node := Node.split 2 T3003 T3014
theorem T3002_ok : Node.check D_R11111 T3002 [((535/512),(535/256)),((999/256),(2331/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3003_ok T3014_ok
def T3001 : Node := Node.split 1 T3002 T3015
theorem T3001_ok : Node.check D_R11111 T3001 [((535/512),(535/256)),((999/256),(333/64)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3002_ok T3015_ok
def T3000 : Node := Node.split 3 T3001 T3016
theorem T3000_ok : Node.check D_R11111 T3000 [((535/512),(535/256)),((999/256),(333/64)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3001_ok T3016_ok
def T2999 : Node := Node.leaf L2999
theorem T2999_ok : Node.check D_R11111 T2999 [((0),(535/512)),((2331/512),(333/64)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2999_ok
def T2998 : Node := Node.leaf L2998
theorem T2998_ok : Node.check D_R11111 T2998 [((0),(535/512)),((999/256),(2331/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2998_ok
def T2997 : Node := Node.leaf L2997
theorem T2997_ok : Node.check D_R11111 T2997 [((535/1024),(535/512)),((999/256),(2331/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2997_ok
def T2996 : Node := Node.leaf L2996
theorem T2996_ok : Node.check D_R11111 T2996 [((0),(535/1024)),((999/256),(2331/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2996_ok
def T2995 : Node := Node.split 0 T2996 T2997
theorem T2995_ok : Node.check D_R11111 T2995 [((0),(535/512)),((999/256),(2331/512)),((0),(333/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2996_ok T2997_ok
def T2994 : Node := Node.split 2 T2995 T2998
theorem T2994_ok : Node.check D_R11111 T2994 [((0),(535/512)),((999/256),(2331/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2995_ok T2998_ok
def T2993 : Node := Node.split 1 T2994 T2999
theorem T2993_ok : Node.check D_R11111 T2993 [((0),(535/512)),((999/256),(333/64)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2994_ok T2999_ok
def T2992 : Node := Node.leaf L2992
theorem T2992_ok : Node.check D_R11111 T2992 [((0),(535/512)),((2331/512),(333/64)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2992_ok
def T2991 : Node := Node.leaf L2991
theorem T2991_ok : Node.check D_R11111 T2991 [((535/1024),(535/512)),((2331/512),(333/64)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2991_ok
def T2990 : Node := Node.leaf L2990
theorem T2990_ok : Node.check D_R11111 T2990 [((535/1024),(535/512)),((4995/1024),(333/64)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2990_ok
def T2989 : Node := Node.leaf L2989
theorem T2989_ok : Node.check D_R11111 T2989 [((535/1024),(535/512)),((2331/512),(4995/1024)),((333/1024),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2989_ok
def T2988 : Node := Node.leaf L2988
theorem T2988_ok : Node.check D_R11111 T2988 [((535/1024),(535/512)),((2331/512),(4995/1024)),((0),(333/1024)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2988_ok
def T2987 : Node := Node.split 2 T2988 T2989
theorem T2987_ok : Node.check D_R11111 T2987 [((535/1024),(535/512)),((2331/512),(4995/1024)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2988_ok T2989_ok
def T2986 : Node := Node.split 1 T2987 T2990
theorem T2986_ok : Node.check D_R11111 T2986 [((535/1024),(535/512)),((2331/512),(333/64)),((0),(333/512)),((0),(535/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2987_ok T2990_ok
def T2985 : Node := Node.split 3 T2986 T2991
theorem T2985_ok : Node.check D_R11111 T2985 [((535/1024),(535/512)),((2331/512),(333/64)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2986_ok T2991_ok
def T2984 : Node := Node.leaf L2984
theorem T2984_ok : Node.check D_R11111 T2984 [((0),(535/1024)),((2331/512),(333/64)),((0),(333/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2984_ok
def T2983 : Node := Node.leaf L2983
theorem T2983_ok : Node.check D_R11111 T2983 [((0),(535/1024)),((2331/512),(333/64)),((0),(333/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2983_ok
def T2982 : Node := Node.split 3 T2983 T2984
theorem T2982_ok : Node.check D_R11111 T2982 [((0),(535/1024)),((2331/512),(333/64)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2983_ok T2984_ok
def T2981 : Node := Node.split 0 T2982 T2985
theorem T2981_ok : Node.check D_R11111 T2981 [((0),(535/512)),((2331/512),(333/64)),((0),(333/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2982_ok T2985_ok
def T2980 : Node := Node.split 2 T2981 T2992
theorem T2980_ok : Node.check D_R11111 T2980 [((0),(535/512)),((2331/512),(333/64)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2981_ok T2992_ok
def T2979 : Node := Node.leaf L2979
theorem T2979_ok : Node.check D_R11111 T2979 [((535/1024),(535/512)),((999/256),(2331/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2979_ok
def T2978 : Node := Node.leaf L2978
theorem T2978_ok : Node.check D_R11111 T2978 [((535/1024),(535/512)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2978_ok
def T2977 : Node := Node.split 3 T2978 T2979
theorem T2977_ok : Node.check D_R11111 T2977 [((535/1024),(535/512)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2978_ok T2979_ok
def T2976 : Node := Node.leaf L2976
theorem T2976_ok : Node.check D_R11111 T2976 [((0),(535/1024)),((999/256),(2331/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2976_ok
def T2975 : Node := Node.leaf L2975
theorem T2975_ok : Node.check D_R11111 T2975 [((0),(535/1024)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2975_ok
def T2974 : Node := Node.split 3 T2975 T2976
theorem T2974_ok : Node.check D_R11111 T2974 [((0),(535/1024)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2975_ok T2976_ok
def T2973 : Node := Node.split 0 T2974 T2977
theorem T2973_ok : Node.check D_R11111 T2973 [((0),(535/512)),((999/256),(2331/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2974_ok T2977_ok
def T2972 : Node := Node.leaf L2972
theorem T2972_ok : Node.check D_R11111 T2972 [((0),(535/512)),((999/256),(2331/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2972_ok
def T2971 : Node := Node.split 2 T2972 T2973
theorem T2971_ok : Node.check D_R11111 T2971 [((0),(535/512)),((999/256),(2331/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2972_ok T2973_ok
def T2970 : Node := Node.split 1 T2971 T2980
theorem T2970_ok : Node.check D_R11111 T2970 [((0),(535/512)),((999/256),(333/64)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2971_ok T2980_ok
def T2969 : Node := Node.split 3 T2970 T2993
theorem T2969_ok : Node.check D_R11111 T2969 [((0),(535/512)),((999/256),(333/64)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2970_ok T2993_ok
def T2968 : Node := Node.split 0 T2969 T3000
theorem T2968_ok : Node.check D_R11111 T2968 [((0),(535/256)),((999/256),(333/64)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2969_ok T3000_ok
def T2967 : Node := Node.split 2 T2968 T3017
theorem T2967_ok : Node.check D_R11111 T2967 [((0),(535/256)),((999/256),(333/64)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2968_ok T3017_ok
def T2966 : Node := Node.leaf L2966
theorem T2966_ok : Node.check D_R11111 T2966 [((535/512),(535/256)),((333/128),(999/256)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2966_ok
def T2965 : Node := Node.leaf L2965
theorem T2965_ok : Node.check D_R11111 T2965 [((535/512),(535/256)),((1665/512),(999/256)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2965_ok
def T2964 : Node := Node.leaf L2964
theorem T2964_ok : Node.check D_R11111 T2964 [((535/512),(535/256)),((333/128),(1665/512)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2964_ok
def T2963 : Node := Node.leaf L2963
theorem T2963_ok : Node.check D_R11111 T2963 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2963_ok
def T2962 : Node := Node.leaf L2962
theorem T2962_ok : Node.check D_R11111 T2962 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2962_ok
def T2961 : Node := Node.split 3 T2962 T2963
theorem T2961_ok : Node.check D_R11111 T2961 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2962_ok T2963_ok
def T2960 : Node := Node.leaf L2960
theorem T2960_ok : Node.check D_R11111 T2960 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2960_ok
def T2959 : Node := Node.leaf L2959
theorem T2959_ok : Node.check D_R11111 T2959 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2959_ok
def T2958 : Node := Node.split 3 T2959 T2960
theorem T2958_ok : Node.check D_R11111 T2958 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2959_ok T2960_ok
def T2957 : Node := Node.split 0 T2958 T2961
theorem T2957_ok : Node.check D_R11111 T2957 [((535/512),(535/256)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2958_ok T2961_ok
def T2956 : Node := Node.split 2 T2957 T2964
theorem T2956_ok : Node.check D_R11111 T2956 [((535/512),(535/256)),((333/128),(1665/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2957_ok T2964_ok
def T2955 : Node := Node.split 1 T2956 T2965
theorem T2955_ok : Node.check D_R11111 T2955 [((535/512),(535/256)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2956_ok T2965_ok
def T2954 : Node := Node.split 3 T2955 T2966
theorem T2954_ok : Node.check D_R11111 T2954 [((535/512),(535/256)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2955_ok T2966_ok
def T2953 : Node := Node.leaf L2953
theorem T2953_ok : Node.check D_R11111 T2953 [((0),(535/512)),((1665/512),(999/256)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2953_ok
def T2952 : Node := Node.leaf L2952
theorem T2952_ok : Node.check D_R11111 T2952 [((0),(535/512)),((333/128),(1665/512)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2952_ok
def T2951 : Node := Node.leaf L2951
theorem T2951_ok : Node.check D_R11111 T2951 [((535/1024),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2951_ok
def T2950 : Node := Node.leaf L2950
theorem T2950_ok : Node.check D_R11111 T2950 [((0),(535/1024)),((333/128),(1665/512)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2950_ok
def T2949 : Node := Node.split 0 T2950 T2951
theorem T2949_ok : Node.check D_R11111 T2949 [((0),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2950_ok T2951_ok
def T2948 : Node := Node.split 2 T2949 T2952
theorem T2948_ok : Node.check D_R11111 T2948 [((0),(535/512)),((333/128),(1665/512)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2949_ok T2952_ok
def T2947 : Node := Node.split 1 T2948 T2953
theorem T2947_ok : Node.check D_R11111 T2947 [((0),(535/512)),((333/128),(999/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2948_ok T2953_ok
def T2946 : Node := Node.leaf L2946
theorem T2946_ok : Node.check D_R11111 T2946 [((0),(535/512)),((1665/512),(999/256)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2946_ok
def T2945 : Node := Node.leaf L2945
theorem T2945_ok : Node.check D_R11111 T2945 [((535/1024),(535/512)),((1665/512),(999/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2945_ok
def T2944 : Node := Node.leaf L2944
theorem T2944_ok : Node.check D_R11111 T2944 [((535/1024),(535/512)),((1665/512),(999/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2944_ok
def T2943 : Node := Node.split 3 T2944 T2945
theorem T2943_ok : Node.check D_R11111 T2943 [((535/1024),(535/512)),((1665/512),(999/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2944_ok T2945_ok
def T2942 : Node := Node.leaf L2942
theorem T2942_ok : Node.check D_R11111 T2942 [((0),(535/1024)),((1665/512),(999/256)),((333/256),(999/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2942_ok
def T2941 : Node := Node.split 0 T2942 T2943
theorem T2941_ok : Node.check D_R11111 T2941 [((0),(535/512)),((1665/512),(999/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2942_ok T2943_ok
def T2940 : Node := Node.split 2 T2941 T2946
theorem T2940_ok : Node.check D_R11111 T2940 [((0),(535/512)),((1665/512),(999/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2941_ok T2946_ok
def T2939 : Node := Node.leaf L2939
theorem T2939_ok : Node.check D_R11111 T2939 [((535/1024),(535/512)),((333/128),(1665/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2939_ok
def T2938 : Node := Node.leaf L2938
theorem T2938_ok : Node.check D_R11111 T2938 [((535/1024),(535/512)),((333/128),(1665/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2938_ok
def T2937 : Node := Node.split 3 T2938 T2939
theorem T2937_ok : Node.check D_R11111 T2937 [((535/1024),(535/512)),((333/128),(1665/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2938_ok T2939_ok
def T2936 : Node := Node.leaf L2936
theorem T2936_ok : Node.check D_R11111 T2936 [((0),(535/1024)),((333/128),(1665/512)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2936_ok
def T2935 : Node := Node.split 0 T2936 T2937
theorem T2935_ok : Node.check D_R11111 T2935 [((0),(535/512)),((333/128),(1665/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2936_ok T2937_ok
def T2934 : Node := Node.leaf L2934
theorem T2934_ok : Node.check D_R11111 T2934 [((535/1024),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2934_ok
def T2933 : Node := Node.leaf L2933
theorem T2933_ok : Node.check D_R11111 T2933 [((535/1024),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2933_ok
def T2932 : Node := Node.split 3 T2933 T2934
theorem T2932_ok : Node.check D_R11111 T2932 [((535/1024),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2933_ok T2934_ok
def T2931 : Node := Node.leaf L2931
theorem T2931_ok : Node.check D_R11111 T2931 [((0),(535/1024)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2931_ok
def T2930 : Node := Node.split 0 T2931 T2932
theorem T2930_ok : Node.check D_R11111 T2930 [((0),(535/512)),((333/128),(1665/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2931_ok T2932_ok
def T2929 : Node := Node.split 2 T2930 T2935
theorem T2929_ok : Node.check D_R11111 T2929 [((0),(535/512)),((333/128),(1665/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2930_ok T2935_ok
def T2928 : Node := Node.split 1 T2929 T2940
theorem T2928_ok : Node.check D_R11111 T2928 [((0),(535/512)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2929_ok T2940_ok
def T2927 : Node := Node.split 3 T2928 T2947
theorem T2927_ok : Node.check D_R11111 T2927 [((0),(535/512)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2928_ok T2947_ok
def T2926 : Node := Node.split 0 T2927 T2954
theorem T2926_ok : Node.check D_R11111 T2926 [((0),(535/256)),((333/128),(999/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2927_ok T2954_ok
def T2925 : Node := Node.leaf L2925
theorem T2925_ok : Node.check D_R11111 T2925 [((535/512),(535/256)),((1665/512),(999/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2925_ok
def T2924 : Node := Node.leaf L2924
theorem T2924_ok : Node.check D_R11111 T2924 [((535/512),(535/256)),((1665/512),(999/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2924_ok
def T2923 : Node := Node.split 2 T2924 T2925
theorem T2923_ok : Node.check D_R11111 T2923 [((535/512),(535/256)),((1665/512),(999/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2924_ok T2925_ok
def T2922 : Node := Node.leaf L2922
theorem T2922_ok : Node.check D_R11111 T2922 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2922_ok
def T2921 : Node := Node.leaf L2921
theorem T2921_ok : Node.check D_R11111 T2921 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2921_ok
def T2920 : Node := Node.leaf L2920
theorem T2920_ok : Node.check D_R11111 T2920 [((535/512),(1605/1024)),((2997/1024),(1665/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2920_ok
def T2919 : Node := Node.leaf L2919
theorem T2919_ok : Node.check D_R11111 T2919 [((535/512),(1605/1024)),((2997/1024),(1665/512)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2919_ok
def T2918 : Node := Node.split 2 T2919 T2920
theorem T2918_ok : Node.check D_R11111 T2918 [((535/512),(1605/1024)),((2997/1024),(1665/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2919_ok T2920_ok
def T2917 : Node := Node.leaf L2917
theorem T2917_ok : Node.check D_R11111 T2917 [((535/512),(1605/1024)),((333/128),(2997/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2917_ok
def T2916 : Node := Node.split 1 T2917 T2918
theorem T2916_ok : Node.check D_R11111 T2916 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2917_ok T2918_ok
def T2915 : Node := Node.split 3 T2916 T2921
theorem T2915_ok : Node.check D_R11111 T2915 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2916_ok T2921_ok
def T2914 : Node := Node.split 0 T2915 T2922
theorem T2914_ok : Node.check D_R11111 T2914 [((535/512),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2915_ok T2922_ok
def T2913 : Node := Node.leaf L2913
theorem T2913_ok : Node.check D_R11111 T2913 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2913_ok
def T2912 : Node := Node.split 2 T2913 T2914
theorem T2912_ok : Node.check D_R11111 T2912 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2913_ok T2914_ok
def T2911 : Node := Node.split 1 T2912 T2923
theorem T2911_ok : Node.check D_R11111 T2911 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2912_ok T2923_ok
def T2910 : Node := Node.leaf L2910
theorem T2910_ok : Node.check D_R11111 T2910 [((1605/1024),(535/256)),((1665/512),(999/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2910_ok
def T2909 : Node := Node.leaf L2909
theorem T2909_ok : Node.check D_R11111 T2909 [((1605/1024),(535/256)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2909_ok
def T2908 : Node := Node.split 3 T2909 T2910
theorem T2908_ok : Node.check D_R11111 T2908 [((1605/1024),(535/256)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2909_ok T2910_ok
def T2907 : Node := Node.leaf L2907
theorem T2907_ok : Node.check D_R11111 T2907 [((535/512),(1605/1024)),((1665/512),(999/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2907_ok
def T2906 : Node := Node.leaf L2906
theorem T2906_ok : Node.check D_R11111 T2906 [((535/512),(1605/1024)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2906_ok
def T2905 : Node := Node.split 3 T2906 T2907
theorem T2905_ok : Node.check D_R11111 T2905 [((535/512),(1605/1024)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2906_ok T2907_ok
def T2904 : Node := Node.split 0 T2905 T2908
theorem T2904_ok : Node.check D_R11111 T2904 [((535/512),(535/256)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2905_ok T2908_ok
def T2903 : Node := Node.leaf L2903
theorem T2903_ok : Node.check D_R11111 T2903 [((535/512),(535/256)),((1665/512),(999/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2903_ok
def T2902 : Node := Node.split 2 T2903 T2904
theorem T2902_ok : Node.check D_R11111 T2902 [((535/512),(535/256)),((1665/512),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2903_ok T2904_ok
def T2901 : Node := Node.leaf L2901
theorem T2901_ok : Node.check D_R11111 T2901 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2901_ok
def T2900 : Node := Node.leaf L2900
theorem T2900_ok : Node.check D_R11111 T2900 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2900_ok
def T2899 : Node := Node.split 3 T2900 T2901
theorem T2899_ok : Node.check D_R11111 T2899 [((1605/1024),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2900_ok T2901_ok
def T2898 : Node := Node.leaf L2898
theorem T2898_ok : Node.check D_R11111 T2898 [((535/512),(1605/1024)),((2997/1024),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2898_ok
def T2897 : Node := Node.leaf L2897
theorem T2897_ok : Node.check D_R11111 T2897 [((535/512),(1605/1024)),((333/128),(2997/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2897_ok
def T2896 : Node := Node.split 1 T2897 T2898
theorem T2896_ok : Node.check D_R11111 T2896 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2897_ok T2898_ok
def T2895 : Node := Node.leaf L2895
theorem T2895_ok : Node.check D_R11111 T2895 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2895_ok
def T2894 : Node := Node.split 3 T2895 T2896
theorem T2894_ok : Node.check D_R11111 T2894 [((535/512),(1605/1024)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2895_ok T2896_ok
def T2893 : Node := Node.split 0 T2894 T2899
theorem T2893_ok : Node.check D_R11111 T2893 [((535/512),(535/256)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2894_ok T2899_ok
def T2892 : Node := Node.leaf L2892
theorem T2892_ok : Node.check D_R11111 T2892 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2892_ok
def T2891 : Node := Node.split 2 T2892 T2893
theorem T2891_ok : Node.check D_R11111 T2891 [((535/512),(535/256)),((333/128),(1665/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2892_ok T2893_ok
def T2890 : Node := Node.split 1 T2891 T2902
theorem T2890_ok : Node.check D_R11111 T2890 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2891_ok T2902_ok
def T2889 : Node := Node.split 3 T2890 T2911
theorem T2889_ok : Node.check D_R11111 T2889 [((535/512),(535/256)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2890_ok T2911_ok
def T2888 : Node := Node.leaf L2888
theorem T2888_ok : Node.check D_R11111 T2888 [((535/1024),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2888_ok
def T2887 : Node := Node.leaf L2887
theorem T2887_ok : Node.check D_R11111 T2887 [((0),(535/1024)),((1665/512),(999/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2887_ok
def T2886 : Node := Node.split 0 T2887 T2888
theorem T2886_ok : Node.check D_R11111 T2886 [((0),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2887_ok T2888_ok
def T2885 : Node := Node.leaf L2885
theorem T2885_ok : Node.check D_R11111 T2885 [((0),(535/512)),((1665/512),(999/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2885_ok
def T2884 : Node := Node.split 2 T2885 T2886
theorem T2884_ok : Node.check D_R11111 T2884 [((0),(535/512)),((1665/512),(999/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2885_ok T2886_ok
def T2883 : Node := Node.leaf L2883
theorem T2883_ok : Node.check D_R11111 T2883 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2883_ok
def T2882 : Node := Node.leaf L2882
theorem T2882_ok : Node.check D_R11111 T2882 [((535/1024),(535/512)),((2997/1024),(1665/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2882_ok
def T2881 : Node := Node.leaf L2881
theorem T2881_ok : Node.check D_R11111 T2881 [((535/1024),(535/512)),((333/128),(2997/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2881_ok
def T2880 : Node := Node.split 1 T2881 T2882
theorem T2880_ok : Node.check D_R11111 T2880 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2881_ok T2882_ok
def T2879 : Node := Node.split 3 T2880 T2883
theorem T2879_ok : Node.check D_R11111 T2879 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2880_ok T2883_ok
def T2878 : Node := Node.leaf L2878
theorem T2878_ok : Node.check D_R11111 T2878 [((0),(535/1024)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2878_ok
def T2877 : Node := Node.split 0 T2878 T2879
theorem T2877_ok : Node.check D_R11111 T2877 [((0),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2878_ok T2879_ok
def T2876 : Node := Node.leaf L2876
theorem T2876_ok : Node.check D_R11111 T2876 [((0),(535/512)),((333/128),(1665/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2876_ok
def T2875 : Node := Node.split 2 T2876 T2877
theorem T2875_ok : Node.check D_R11111 T2875 [((0),(535/512)),((333/128),(1665/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2876_ok T2877_ok
def T2874 : Node := Node.split 1 T2875 T2884
theorem T2874_ok : Node.check D_R11111 T2874 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2875_ok T2884_ok
def T2873 : Node := Node.leaf L2873
theorem T2873_ok : Node.check D_R11111 T2873 [((535/1024),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2873_ok
def T2872 : Node := Node.leaf L2872
theorem T2872_ok : Node.check D_R11111 T2872 [((535/1024),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2872_ok
def T2871 : Node := Node.split 3 T2872 T2873
theorem T2871_ok : Node.check D_R11111 T2871 [((535/1024),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2872_ok T2873_ok
def T2870 : Node := Node.leaf L2870
theorem T2870_ok : Node.check D_R11111 T2870 [((0),(535/1024)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2870_ok
def T2869 : Node := Node.split 0 T2870 T2871
theorem T2869_ok : Node.check D_R11111 T2869 [((0),(535/512)),((1665/512),(999/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2870_ok T2871_ok
def T2868 : Node := Node.leaf L2868
theorem T2868_ok : Node.check D_R11111 T2868 [((0),(535/512)),((1665/512),(999/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2868_ok
def T2867 : Node := Node.split 2 T2868 T2869
theorem T2867_ok : Node.check D_R11111 T2867 [((0),(535/512)),((1665/512),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2868_ok T2869_ok
def T2866 : Node := Node.leaf L2866
theorem T2866_ok : Node.check D_R11111 T2866 [((535/1024),(535/512)),((2997/1024),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2866_ok
def T2865 : Node := Node.leaf L2865
theorem T2865_ok : Node.check D_R11111 T2865 [((535/1024),(535/512)),((333/128),(2997/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2865_ok
def T2864 : Node := Node.split 1 T2865 T2866
theorem T2864_ok : Node.check D_R11111 T2864 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2865_ok T2866_ok
def T2863 : Node := Node.leaf L2863
theorem T2863_ok : Node.check D_R11111 T2863 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2863_ok
def T2862 : Node := Node.split 3 T2863 T2864
theorem T2862_ok : Node.check D_R11111 T2862 [((535/1024),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2863_ok T2864_ok
def T2861 : Node := Node.leaf L2861
theorem T2861_ok : Node.check D_R11111 T2861 [((0),(535/1024)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2861_ok
def T2860 : Node := Node.split 0 T2861 T2862
theorem T2860_ok : Node.check D_R11111 T2860 [((0),(535/512)),((333/128),(1665/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2861_ok T2862_ok
def T2859 : Node := Node.leaf L2859
theorem T2859_ok : Node.check D_R11111 T2859 [((0),(535/512)),((333/128),(1665/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2859_ok
def T2858 : Node := Node.split 2 T2859 T2860
theorem T2858_ok : Node.check D_R11111 T2858 [((0),(535/512)),((333/128),(1665/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2859_ok T2860_ok
def T2857 : Node := Node.split 1 T2858 T2867
theorem T2857_ok : Node.check D_R11111 T2857 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2858_ok T2867_ok
def T2856 : Node := Node.split 3 T2857 T2874
theorem T2856_ok : Node.check D_R11111 T2856 [((0),(535/512)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2857_ok T2874_ok
def T2855 : Node := Node.split 0 T2856 T2889
theorem T2855_ok : Node.check D_R11111 T2855 [((0),(535/256)),((333/128),(999/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2856_ok T2889_ok
def T2854 : Node := Node.split 2 T2855 T2926
theorem T2854_ok : Node.check D_R11111 T2854 [((0),(535/256)),((333/128),(999/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2855_ok T2926_ok
def T2853 : Node := Node.split 1 T2854 T2967
theorem T2853_ok : Node.check D_R11111 T2853 [((0),(535/256)),((333/128),(333/64)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2854_ok T2967_ok
def T2852 : Node := Node.split 3 T2853 T3018
theorem T2852_ok : Node.check D_R11111 T2852 [((0),(535/256)),((333/128),(333/64)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2853_ok T3018_ok
def T2851 : Node := Node.split 0 T2852 T3049
theorem T2851_ok : Node.check D_R11111 T2851 [((0),(535/128)),((333/128),(333/64)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2852_ok T3049_ok
def T2850 : Node := Node.split 2 T2851 T3102
theorem T2850_ok : Node.check D_R11111 T2850 [((0),(535/128)),((333/128),(333/64)),((0),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2851_ok T3102_ok
def T2849 : Node := Node.leaf L2849
theorem T2849_ok : Node.check D_R11111 T2849 [((535/256),(535/128)),((0),(333/128)),((333/128),(333/64)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L2849_ok
def T2848 : Node := Node.leaf L2848
theorem T2848_ok : Node.check D_R11111 T2848 [((535/256),(535/128)),((333/256),(333/128)),((333/128),(333/64)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L2848_ok
def T2847 : Node := Node.leaf L2847
theorem T2847_ok : Node.check D_R11111 T2847 [((535/256),(535/128)),((0),(333/256)),((999/256),(333/64)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L2847_ok
def T2846 : Node := Node.leaf L2846
theorem T2846_ok : Node.check D_R11111 T2846 [((1605/512),(535/128)),((0),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2846_ok
def T2845 : Node := Node.leaf L2845
theorem T2845_ok : Node.check D_R11111 T2845 [((1605/512),(535/128)),((333/512),(333/256)),((333/128),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2845_ok
def T2844 : Node := Node.leaf L2844
theorem T2844_ok : Node.check D_R11111 T2844 [((1605/512),(535/128)),((0),(333/512)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2844_ok
def T2843 : Node := Node.leaf L2843
theorem T2843_ok : Node.check D_R11111 T2843 [((3745/1024),(535/128)),((0),(333/512)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2843_ok
def T2842 : Node := Node.leaf L2842
theorem T2842_ok : Node.check D_R11111 T2842 [((3745/1024),(535/128)),((0),(333/512)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2842_ok
def T2841 : Node := Node.split 3 T2842 T2843
theorem T2841_ok : Node.check D_R11111 T2841 [((3745/1024),(535/128)),((0),(333/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2842_ok T2843_ok
def T2840 : Node := Node.leaf L2840
theorem T2840_ok : Node.check D_R11111 T2840 [((1605/512),(3745/1024)),((0),(333/512)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2840_ok
def T2839 : Node := Node.leaf L2839
theorem T2839_ok : Node.check D_R11111 T2839 [((1605/512),(3745/1024)),((0),(333/512)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2839_ok
def T2838 : Node := Node.split 3 T2839 T2840
theorem T2838_ok : Node.check D_R11111 T2838 [((1605/512),(3745/1024)),((0),(333/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2839_ok T2840_ok
def T2837 : Node := Node.split 0 T2838 T2841
theorem T2837_ok : Node.check D_R11111 T2837 [((1605/512),(535/128)),((0),(333/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2838_ok T2841_ok
def T2836 : Node := Node.split 2 T2837 T2844
theorem T2836_ok : Node.check D_R11111 T2836 [((1605/512),(535/128)),((0),(333/512)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2837_ok T2844_ok
def T2835 : Node := Node.split 1 T2836 T2845
theorem T2835_ok : Node.check D_R11111 T2835 [((1605/512),(535/128)),((0),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2836_ok T2845_ok
def T2834 : Node := Node.split 3 T2835 T2846
theorem T2834_ok : Node.check D_R11111 T2834 [((1605/512),(535/128)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2835_ok T2846_ok
def T2833 : Node := Node.leaf L2833
theorem T2833_ok : Node.check D_R11111 T2833 [((535/256),(1605/512)),((333/512),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2833_ok
def T2832 : Node := Node.leaf L2832
theorem T2832_ok : Node.check D_R11111 T2832 [((535/256),(1605/512)),((0),(333/512)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2832_ok
def T2831 : Node := Node.split 1 T2832 T2833
theorem T2831_ok : Node.check D_R11111 T2831 [((535/256),(1605/512)),((0),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2832_ok T2833_ok
def T2830 : Node := Node.leaf L2830
theorem T2830_ok : Node.check D_R11111 T2830 [((535/256),(1605/512)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2830_ok
def T2829 : Node := Node.leaf L2829
theorem T2829_ok : Node.check D_R11111 T2829 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2829_ok
def T2828 : Node := Node.leaf L2828
theorem T2828_ok : Node.check D_R11111 T2828 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2828_ok
def T2827 : Node := Node.split 3 T2828 T2829
theorem T2827_ok : Node.check D_R11111 T2827 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2828_ok T2829_ok
def T2826 : Node := Node.leaf L2826
theorem T2826_ok : Node.check D_R11111 T2826 [((535/256),(2675/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2826_ok
def T2825 : Node := Node.leaf L2825
theorem T2825_ok : Node.check D_R11111 T2825 [((535/256),(2675/1024)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2825_ok
def T2824 : Node := Node.split 3 T2825 T2826
theorem T2824_ok : Node.check D_R11111 T2824 [((535/256),(2675/1024)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2825_ok T2826_ok
def T2823 : Node := Node.split 0 T2824 T2827
theorem T2823_ok : Node.check D_R11111 T2823 [((535/256),(1605/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2824_ok T2827_ok
def T2822 : Node := Node.split 2 T2823 T2830
theorem T2822_ok : Node.check D_R11111 T2822 [((535/256),(1605/512)),((333/512),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2823_ok T2830_ok
def T2821 : Node := Node.leaf L2821
theorem T2821_ok : Node.check D_R11111 T2821 [((535/256),(1605/512)),((0),(333/512)),((333/128),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2821_ok
def T2820 : Node := Node.split 1 T2821 T2822
theorem T2820_ok : Node.check D_R11111 T2820 [((535/256),(1605/512)),((0),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2821_ok T2822_ok
def T2819 : Node := Node.split 3 T2820 T2831
theorem T2819_ok : Node.check D_R11111 T2819 [((535/256),(1605/512)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2820_ok T2831_ok
def T2818 : Node := Node.split 0 T2819 T2834
theorem T2818_ok : Node.check D_R11111 T2818 [((535/256),(535/128)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2819_ok T2834_ok
def T2817 : Node := Node.split 2 T2818 T2847
theorem T2817_ok : Node.check D_R11111 T2817 [((535/256),(535/128)),((0),(333/256)),((333/128),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2818_ok T2847_ok
def T2816 : Node := Node.split 1 T2817 T2848
theorem T2816_ok : Node.check D_R11111 T2816 [((535/256),(535/128)),((0),(333/128)),((333/128),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2817_ok T2848_ok
def T2815 : Node := Node.split 3 T2816 T2849
theorem T2815_ok : Node.check D_R11111 T2815 [((535/256),(535/128)),((0),(333/128)),((333/128),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2816_ok T2849_ok
def T2814 : Node := Node.leaf L2814
theorem T2814_ok : Node.check D_R11111 T2814 [((0),(535/256)),((333/256),(333/128)),((333/128),(333/64)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L2814_ok
def T2813 : Node := Node.leaf L2813
theorem T2813_ok : Node.check D_R11111 T2813 [((0),(535/256)),((0),(333/256)),((999/256),(333/64)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L2813_ok
def T2812 : Node := Node.leaf L2812
theorem T2812_ok : Node.check D_R11111 T2812 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2812_ok
def T2811 : Node := Node.leaf L2811
theorem T2811_ok : Node.check D_R11111 T2811 [((535/512),(535/256)),((333/512),(333/256)),((333/128),(999/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2811_ok
def T2810 : Node := Node.leaf L2810
theorem T2810_ok : Node.check D_R11111 T2810 [((535/512),(535/256)),((0),(333/512)),((333/128),(999/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2810_ok
def T2809 : Node := Node.split 1 T2810 T2811
theorem T2809_ok : Node.check D_R11111 T2809 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2810_ok T2811_ok
def T2808 : Node := Node.split 3 T2809 T2812
theorem T2808_ok : Node.check D_R11111 T2808 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2809_ok T2812_ok
def T2807 : Node := Node.leaf L2807
theorem T2807_ok : Node.check D_R11111 T2807 [((0),(535/512)),((333/512),(333/256)),((333/128),(999/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2807_ok
def T2806 : Node := Node.leaf L2806
theorem T2806_ok : Node.check D_R11111 T2806 [((0),(535/512)),((0),(333/512)),((1665/512),(999/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2806_ok
def T2805 : Node := Node.leaf L2805
theorem T2805_ok : Node.check D_R11111 T2805 [((535/1024),(535/512)),((0),(333/512)),((333/128),(1665/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2805_ok
def T2804 : Node := Node.leaf L2804
theorem T2804_ok : Node.check D_R11111 T2804 [((0),(535/1024)),((0),(333/512)),((333/128),(1665/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2804_ok
def T2803 : Node := Node.split 0 T2804 T2805
theorem T2803_ok : Node.check D_R11111 T2803 [((0),(535/512)),((0),(333/512)),((333/128),(1665/512)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2804_ok T2805_ok
def T2802 : Node := Node.split 2 T2803 T2806
theorem T2802_ok : Node.check D_R11111 T2802 [((0),(535/512)),((0),(333/512)),((333/128),(999/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2803_ok T2806_ok
def T2801 : Node := Node.split 1 T2802 T2807
theorem T2801_ok : Node.check D_R11111 T2801 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2802_ok T2807_ok
def T2800 : Node := Node.leaf L2800
theorem T2800_ok : Node.check D_R11111 T2800 [((0),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2800_ok
def T2799 : Node := Node.leaf L2799
theorem T2799_ok : Node.check D_R11111 T2799 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2799_ok
def T2798 : Node := Node.leaf L2798
theorem T2798_ok : Node.check D_R11111 T2798 [((0),(535/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2798_ok
def T2797 : Node := Node.split 0 T2798 T2799
theorem T2797_ok : Node.check D_R11111 T2797 [((0),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2798_ok T2799_ok
def T2796 : Node := Node.split 2 T2797 T2800
theorem T2796_ok : Node.check D_R11111 T2796 [((0),(535/512)),((333/512),(333/256)),((333/128),(999/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2797_ok T2800_ok
def T2795 : Node := Node.leaf L2795
theorem T2795_ok : Node.check D_R11111 T2795 [((0),(535/512)),((0),(333/512)),((333/128),(999/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2795_ok
def T2794 : Node := Node.split 1 T2795 T2796
theorem T2794_ok : Node.check D_R11111 T2794 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2795_ok T2796_ok
def T2793 : Node := Node.split 3 T2794 T2801
theorem T2793_ok : Node.check D_R11111 T2793 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2794_ok T2801_ok
def T2792 : Node := Node.split 0 T2793 T2808
theorem T2792_ok : Node.check D_R11111 T2792 [((0),(535/256)),((0),(333/256)),((333/128),(999/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2793_ok T2808_ok
def T2791 : Node := Node.split 2 T2792 T2813
theorem T2791_ok : Node.check D_R11111 T2791 [((0),(535/256)),((0),(333/256)),((333/128),(333/64)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2792_ok T2813_ok
def T2790 : Node := Node.split 1 T2791 T2814
theorem T2790_ok : Node.check D_R11111 T2790 [((0),(535/256)),((0),(333/128)),((333/128),(333/64)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2791_ok T2814_ok
def T2789 : Node := Node.leaf L2789
theorem T2789_ok : Node.check D_R11111 T2789 [((0),(535/256)),((333/256),(333/128)),((999/256),(333/64)),((0),(535/256))] = true := Node.check_leaf_of _ _ _ L2789_ok
def T2788 : Node := Node.leaf L2788
theorem T2788_ok : Node.check D_R11111 T2788 [((535/512),(535/256)),((333/256),(333/128)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2788_ok
def T2787 : Node := Node.leaf L2787
theorem T2787_ok : Node.check D_R11111 T2787 [((535/512),(535/256)),((999/512),(333/128)),((333/128),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2787_ok
def T2786 : Node := Node.leaf L2786
theorem T2786_ok : Node.check D_R11111 T2786 [((535/512),(535/256)),((333/256),(999/512)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2786_ok
def T2785 : Node := Node.leaf L2785
theorem T2785_ok : Node.check D_R11111 T2785 [((1605/1024),(535/256)),((333/256),(999/512)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2785_ok
def T2784 : Node := Node.leaf L2784
theorem T2784_ok : Node.check D_R11111 T2784 [((1605/1024),(535/256)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2784_ok
def T2783 : Node := Node.split 3 T2784 T2785
theorem T2783_ok : Node.check D_R11111 T2783 [((1605/1024),(535/256)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2784_ok T2785_ok
def T2782 : Node := Node.leaf L2782
theorem T2782_ok : Node.check D_R11111 T2782 [((535/512),(1605/1024)),((333/256),(999/512)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2782_ok
def T2781 : Node := Node.leaf L2781
theorem T2781_ok : Node.check D_R11111 T2781 [((535/512),(1605/1024)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2781_ok
def T2780 : Node := Node.split 3 T2781 T2782
theorem T2780_ok : Node.check D_R11111 T2780 [((535/512),(1605/1024)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2781_ok T2782_ok
def T2779 : Node := Node.split 0 T2780 T2783
theorem T2779_ok : Node.check D_R11111 T2779 [((535/512),(535/256)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2780_ok T2783_ok
def T2778 : Node := Node.split 2 T2779 T2786
theorem T2778_ok : Node.check D_R11111 T2778 [((535/512),(535/256)),((333/256),(999/512)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2779_ok T2786_ok
def T2777 : Node := Node.split 1 T2778 T2787
theorem T2777_ok : Node.check D_R11111 T2777 [((535/512),(535/256)),((333/256),(333/128)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2778_ok T2787_ok
def T2776 : Node := Node.split 3 T2777 T2788
theorem T2776_ok : Node.check D_R11111 T2776 [((535/512),(535/256)),((333/256),(333/128)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2777_ok T2788_ok
def T2775 : Node := Node.leaf L2775
theorem T2775_ok : Node.check D_R11111 T2775 [((0),(535/512)),((999/512),(333/128)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2775_ok
def T2774 : Node := Node.leaf L2774
theorem T2774_ok : Node.check D_R11111 T2774 [((0),(535/512)),((333/256),(999/512)),((1665/512),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2774_ok
def T2773 : Node := Node.leaf L2773
theorem T2773_ok : Node.check D_R11111 T2773 [((535/1024),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2773_ok
def T2772 : Node := Node.leaf L2772
theorem T2772_ok : Node.check D_R11111 T2772 [((0),(535/1024)),((333/256),(999/512)),((333/128),(1665/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2772_ok
def T2771 : Node := Node.split 0 T2772 T2773
theorem T2771_ok : Node.check D_R11111 T2771 [((0),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2772_ok T2773_ok
def T2770 : Node := Node.split 2 T2771 T2774
theorem T2770_ok : Node.check D_R11111 T2770 [((0),(535/512)),((333/256),(999/512)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2771_ok T2774_ok
def T2769 : Node := Node.split 1 T2770 T2775
theorem T2769_ok : Node.check D_R11111 T2769 [((0),(535/512)),((333/256),(333/128)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2770_ok T2775_ok
def T2768 : Node := Node.leaf L2768
theorem T2768_ok : Node.check D_R11111 T2768 [((0),(535/512)),((999/512),(333/128)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2768_ok
def T2767 : Node := Node.leaf L2767
theorem T2767_ok : Node.check D_R11111 T2767 [((535/1024),(535/512)),((999/512),(333/128)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2767_ok
def T2766 : Node := Node.leaf L2766
theorem T2766_ok : Node.check D_R11111 T2766 [((535/1024),(535/512)),((999/512),(333/128)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2766_ok
def T2765 : Node := Node.split 3 T2766 T2767
theorem T2765_ok : Node.check D_R11111 T2765 [((535/1024),(535/512)),((999/512),(333/128)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2766_ok T2767_ok
def T2764 : Node := Node.leaf L2764
theorem T2764_ok : Node.check D_R11111 T2764 [((0),(535/1024)),((999/512),(333/128)),((333/128),(1665/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2764_ok
def T2763 : Node := Node.split 0 T2764 T2765
theorem T2763_ok : Node.check D_R11111 T2763 [((0),(535/512)),((999/512),(333/128)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2764_ok T2765_ok
def T2762 : Node := Node.split 2 T2763 T2768
theorem T2762_ok : Node.check D_R11111 T2762 [((0),(535/512)),((999/512),(333/128)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2763_ok T2768_ok
def T2761 : Node := Node.leaf L2761
theorem T2761_ok : Node.check D_R11111 T2761 [((535/1024),(535/512)),((333/256),(999/512)),((1665/512),(999/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2761_ok
def T2760 : Node := Node.leaf L2760
theorem T2760_ok : Node.check D_R11111 T2760 [((535/1024),(535/512)),((333/256),(999/512)),((1665/512),(999/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2760_ok
def T2759 : Node := Node.split 3 T2760 T2761
theorem T2759_ok : Node.check D_R11111 T2759 [((535/1024),(535/512)),((333/256),(999/512)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2760_ok T2761_ok
def T2758 : Node := Node.leaf L2758
theorem T2758_ok : Node.check D_R11111 T2758 [((0),(535/1024)),((333/256),(999/512)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2758_ok
def T2757 : Node := Node.split 0 T2758 T2759
theorem T2757_ok : Node.check D_R11111 T2757 [((0),(535/512)),((333/256),(999/512)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2758_ok T2759_ok
def T2756 : Node := Node.leaf L2756
theorem T2756_ok : Node.check D_R11111 T2756 [((535/1024),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2756_ok
def T2755 : Node := Node.leaf L2755
theorem T2755_ok : Node.check D_R11111 T2755 [((535/1024),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2755_ok
def T2754 : Node := Node.split 3 T2755 T2756
theorem T2754_ok : Node.check D_R11111 T2754 [((535/1024),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2755_ok T2756_ok
def T2753 : Node := Node.leaf L2753
theorem T2753_ok : Node.check D_R11111 T2753 [((0),(535/1024)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2753_ok
def T2752 : Node := Node.split 0 T2753 T2754
theorem T2752_ok : Node.check D_R11111 T2752 [((0),(535/512)),((333/256),(999/512)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2753_ok T2754_ok
def T2751 : Node := Node.split 2 T2752 T2757
theorem T2751_ok : Node.check D_R11111 T2751 [((0),(535/512)),((333/256),(999/512)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2752_ok T2757_ok
def T2750 : Node := Node.split 1 T2751 T2762
theorem T2750_ok : Node.check D_R11111 T2750 [((0),(535/512)),((333/256),(333/128)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2751_ok T2762_ok
def T2749 : Node := Node.split 3 T2750 T2769
theorem T2749_ok : Node.check D_R11111 T2749 [((0),(535/512)),((333/256),(333/128)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2750_ok T2769_ok
def T2748 : Node := Node.split 0 T2749 T2776
theorem T2748_ok : Node.check D_R11111 T2748 [((0),(535/256)),((333/256),(333/128)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2749_ok T2776_ok
def T2747 : Node := Node.split 2 T2748 T2789
theorem T2747_ok : Node.check D_R11111 T2747 [((0),(535/256)),((333/256),(333/128)),((333/128),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2748_ok T2789_ok
def T2746 : Node := Node.leaf L2746
theorem T2746_ok : Node.check D_R11111 T2746 [((535/512),(535/256)),((0),(333/256)),((999/256),(333/64)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2746_ok
def T2745 : Node := Node.leaf L2745
theorem T2745_ok : Node.check D_R11111 T2745 [((535/512),(535/256)),((333/512),(333/256)),((999/256),(333/64)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2745_ok
def T2744 : Node := Node.leaf L2744
theorem T2744_ok : Node.check D_R11111 T2744 [((535/512),(535/256)),((0),(333/512)),((2331/512),(333/64)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2744_ok
def T2743 : Node := Node.leaf L2743
theorem T2743_ok : Node.check D_R11111 T2743 [((1605/1024),(535/256)),((0),(333/512)),((999/256),(2331/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2743_ok
def T2742 : Node := Node.leaf L2742
theorem T2742_ok : Node.check D_R11111 T2742 [((1605/1024),(535/256)),((0),(333/512)),((999/256),(2331/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2742_ok
def T2741 : Node := Node.split 3 T2742 T2743
theorem T2741_ok : Node.check D_R11111 T2741 [((1605/1024),(535/256)),((0),(333/512)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2742_ok T2743_ok
def T2740 : Node := Node.leaf L2740
theorem T2740_ok : Node.check D_R11111 T2740 [((535/512),(1605/1024)),((0),(333/512)),((999/256),(2331/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2740_ok
def T2739 : Node := Node.leaf L2739
theorem T2739_ok : Node.check D_R11111 T2739 [((535/512),(1605/1024)),((0),(333/512)),((999/256),(2331/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2739_ok
def T2738 : Node := Node.split 3 T2739 T2740
theorem T2738_ok : Node.check D_R11111 T2738 [((535/512),(1605/1024)),((0),(333/512)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2739_ok T2740_ok
def T2737 : Node := Node.split 0 T2738 T2741
theorem T2737_ok : Node.check D_R11111 T2737 [((535/512),(535/256)),((0),(333/512)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2738_ok T2741_ok
def T2736 : Node := Node.split 2 T2737 T2744
theorem T2736_ok : Node.check D_R11111 T2736 [((535/512),(535/256)),((0),(333/512)),((999/256),(333/64)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2737_ok T2744_ok
def T2735 : Node := Node.split 1 T2736 T2745
theorem T2735_ok : Node.check D_R11111 T2735 [((535/512),(535/256)),((0),(333/256)),((999/256),(333/64)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2736_ok T2745_ok
def T2734 : Node := Node.split 3 T2735 T2746
theorem T2734_ok : Node.check D_R11111 T2734 [((535/512),(535/256)),((0),(333/256)),((999/256),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2735_ok T2746_ok
def T2733 : Node := Node.leaf L2733
theorem T2733_ok : Node.check D_R11111 T2733 [((0),(535/512)),((333/512),(333/256)),((999/256),(333/64)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2733_ok
def T2732 : Node := Node.leaf L2732
theorem T2732_ok : Node.check D_R11111 T2732 [((0),(535/512)),((0),(333/512)),((2331/512),(333/64)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2732_ok
def T2731 : Node := Node.leaf L2731
theorem T2731_ok : Node.check D_R11111 T2731 [((535/1024),(535/512)),((0),(333/512)),((999/256),(2331/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2731_ok
def T2730 : Node := Node.leaf L2730
theorem T2730_ok : Node.check D_R11111 T2730 [((0),(535/1024)),((0),(333/512)),((999/256),(2331/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2730_ok
def T2729 : Node := Node.split 0 T2730 T2731
theorem T2729_ok : Node.check D_R11111 T2729 [((0),(535/512)),((0),(333/512)),((999/256),(2331/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2730_ok T2731_ok
def T2728 : Node := Node.split 2 T2729 T2732
theorem T2728_ok : Node.check D_R11111 T2728 [((0),(535/512)),((0),(333/512)),((999/256),(333/64)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2729_ok T2732_ok
def T2727 : Node := Node.split 1 T2728 T2733
theorem T2727_ok : Node.check D_R11111 T2727 [((0),(535/512)),((0),(333/256)),((999/256),(333/64)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2728_ok T2733_ok
def T2726 : Node := Node.leaf L2726
theorem T2726_ok : Node.check D_R11111 T2726 [((0),(535/512)),((333/512),(333/256)),((2331/512),(333/64)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2726_ok
def T2725 : Node := Node.leaf L2725
theorem T2725_ok : Node.check D_R11111 T2725 [((535/1024),(535/512)),((333/512),(333/256)),((999/256),(2331/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2725_ok
def T2724 : Node := Node.leaf L2724
theorem T2724_ok : Node.check D_R11111 T2724 [((535/1024),(535/512)),((333/512),(333/256)),((999/256),(2331/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2724_ok
def T2723 : Node := Node.split 3 T2724 T2725
theorem T2723_ok : Node.check D_R11111 T2723 [((535/1024),(535/512)),((333/512),(333/256)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2724_ok T2725_ok
def T2722 : Node := Node.leaf L2722
theorem T2722_ok : Node.check D_R11111 T2722 [((0),(535/1024)),((333/512),(333/256)),((999/256),(2331/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2722_ok
def T2721 : Node := Node.leaf L2721
theorem T2721_ok : Node.check D_R11111 T2721 [((0),(535/1024)),((333/512),(333/256)),((999/256),(2331/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2721_ok
def T2720 : Node := Node.split 3 T2721 T2722
theorem T2720_ok : Node.check D_R11111 T2720 [((0),(535/1024)),((333/512),(333/256)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2721_ok T2722_ok
def T2719 : Node := Node.split 0 T2720 T2723
theorem T2719_ok : Node.check D_R11111 T2719 [((0),(535/512)),((333/512),(333/256)),((999/256),(2331/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2720_ok T2723_ok
def T2718 : Node := Node.split 2 T2719 T2726
theorem T2718_ok : Node.check D_R11111 T2718 [((0),(535/512)),((333/512),(333/256)),((999/256),(333/64)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2719_ok T2726_ok
def T2717 : Node := Node.leaf L2717
theorem T2717_ok : Node.check D_R11111 T2717 [((0),(535/512)),((0),(333/512)),((999/256),(333/64)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2717_ok
def T2716 : Node := Node.split 1 T2717 T2718
theorem T2716_ok : Node.check D_R11111 T2716 [((0),(535/512)),((0),(333/256)),((999/256),(333/64)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2717_ok T2718_ok
def T2715 : Node := Node.split 3 T2716 T2727
theorem T2715_ok : Node.check D_R11111 T2715 [((0),(535/512)),((0),(333/256)),((999/256),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2716_ok T2727_ok
def T2714 : Node := Node.split 0 T2715 T2734
theorem T2714_ok : Node.check D_R11111 T2714 [((0),(535/256)),((0),(333/256)),((999/256),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2715_ok T2734_ok
def T2713 : Node := Node.leaf L2713
theorem T2713_ok : Node.check D_R11111 T2713 [((535/512),(535/256)),((333/512),(333/256)),((1665/512),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2713_ok
def T2712 : Node := Node.leaf L2712
theorem T2712_ok : Node.check D_R11111 T2712 [((1605/1024),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2712_ok
def T2711 : Node := Node.leaf L2711
theorem T2711_ok : Node.check D_R11111 T2711 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2711_ok
def T2710 : Node := Node.leaf L2710
theorem T2710_ok : Node.check D_R11111 T2710 [((535/512),(1605/1024)),((999/1024),(333/256)),((2997/1024),(1665/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2710_ok
def T2709 : Node := Node.leaf L2709
theorem T2709_ok : Node.check D_R11111 T2709 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/128),(2997/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2709_ok
def T2708 : Node := Node.split 2 T2709 T2710
theorem T2708_ok : Node.check D_R11111 T2708 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/128),(1665/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2709_ok T2710_ok
def T2707 : Node := Node.leaf L2707
theorem T2707_ok : Node.check D_R11111 T2707 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/128),(1665/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2707_ok
def T2706 : Node := Node.split 1 T2707 T2708
theorem T2706_ok : Node.check D_R11111 T2706 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2707_ok T2708_ok
def T2705 : Node := Node.split 3 T2706 T2711
theorem T2705_ok : Node.check D_R11111 T2705 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2706_ok T2711_ok
def T2704 : Node := Node.split 0 T2705 T2712
theorem T2704_ok : Node.check D_R11111 T2704 [((535/512),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2705_ok T2712_ok
def T2703 : Node := Node.split 2 T2704 T2713
theorem T2703_ok : Node.check D_R11111 T2703 [((535/512),(535/256)),((333/512),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2704_ok T2713_ok
def T2702 : Node := Node.leaf L2702
theorem T2702_ok : Node.check D_R11111 T2702 [((535/512),(535/256)),((0),(333/512)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2702_ok
def T2701 : Node := Node.split 1 T2702 T2703
theorem T2701_ok : Node.check D_R11111 T2701 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2702_ok T2703_ok
def T2700 : Node := Node.leaf L2700
theorem T2700_ok : Node.check D_R11111 T2700 [((1605/1024),(535/256)),((333/512),(333/256)),((1665/512),(999/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2700_ok
def T2699 : Node := Node.leaf L2699
theorem T2699_ok : Node.check D_R11111 T2699 [((1605/1024),(535/256)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2699_ok
def T2698 : Node := Node.split 3 T2699 T2700
theorem T2698_ok : Node.check D_R11111 T2698 [((1605/1024),(535/256)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2699_ok T2700_ok
def T2697 : Node := Node.leaf L2697
theorem T2697_ok : Node.check D_R11111 T2697 [((535/512),(1605/1024)),((333/512),(333/256)),((1665/512),(999/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2697_ok
def T2696 : Node := Node.leaf L2696
theorem T2696_ok : Node.check D_R11111 T2696 [((535/512),(1605/1024)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2696_ok
def T2695 : Node := Node.split 3 T2696 T2697
theorem T2695_ok : Node.check D_R11111 T2695 [((535/512),(1605/1024)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2696_ok T2697_ok
def T2694 : Node := Node.split 0 T2695 T2698
theorem T2694_ok : Node.check D_R11111 T2694 [((535/512),(535/256)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2695_ok T2698_ok
def T2693 : Node := Node.leaf L2693
theorem T2693_ok : Node.check D_R11111 T2693 [((1605/1024),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2693_ok
def T2692 : Node := Node.leaf L2692
theorem T2692_ok : Node.check D_R11111 T2692 [((1605/1024),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2692_ok
def T2691 : Node := Node.split 3 T2692 T2693
theorem T2691_ok : Node.check D_R11111 T2691 [((1605/1024),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2692_ok T2693_ok
def T2690 : Node := Node.leaf L2690
theorem T2690_ok : Node.check D_R11111 T2690 [((535/512),(1605/1024)),((999/1024),(333/256)),((2997/1024),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2690_ok
def T2689 : Node := Node.leaf L2689
theorem T2689_ok : Node.check D_R11111 T2689 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/128),(2997/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2689_ok
def T2688 : Node := Node.split 2 T2689 T2690
theorem T2688_ok : Node.check D_R11111 T2688 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2689_ok T2690_ok
def T2687 : Node := Node.leaf L2687
theorem T2687_ok : Node.check D_R11111 T2687 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2687_ok
def T2686 : Node := Node.split 1 T2687 T2688
theorem T2686_ok : Node.check D_R11111 T2686 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2687_ok T2688_ok
def T2685 : Node := Node.leaf L2685
theorem T2685_ok : Node.check D_R11111 T2685 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2685_ok
def T2684 : Node := Node.split 3 T2685 T2686
theorem T2684_ok : Node.check D_R11111 T2684 [((535/512),(1605/1024)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2685_ok T2686_ok
def T2683 : Node := Node.split 0 T2684 T2691
theorem T2683_ok : Node.check D_R11111 T2683 [((535/512),(535/256)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2684_ok T2691_ok
def T2682 : Node := Node.split 2 T2683 T2694
theorem T2682_ok : Node.check D_R11111 T2682 [((535/512),(535/256)),((333/512),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2683_ok T2694_ok
def T2681 : Node := Node.leaf L2681
theorem T2681_ok : Node.check D_R11111 T2681 [((535/512),(535/256)),((0),(333/512)),((333/128),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2681_ok
def T2680 : Node := Node.split 1 T2681 T2682
theorem T2680_ok : Node.check D_R11111 T2680 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2681_ok T2682_ok
def T2679 : Node := Node.split 3 T2680 T2701
theorem T2679_ok : Node.check D_R11111 T2679 [((535/512),(535/256)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2680_ok T2701_ok
def T2678 : Node := Node.leaf L2678
theorem T2678_ok : Node.check D_R11111 T2678 [((535/1024),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2678_ok
def T2677 : Node := Node.leaf L2677
theorem T2677_ok : Node.check D_R11111 T2677 [((0),(535/1024)),((333/512),(333/256)),((1665/512),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2677_ok
def T2676 : Node := Node.split 0 T2677 T2678
theorem T2676_ok : Node.check D_R11111 T2676 [((0),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2677_ok T2678_ok
def T2675 : Node := Node.leaf L2675
theorem T2675_ok : Node.check D_R11111 T2675 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2675_ok
def T2674 : Node := Node.leaf L2674
theorem T2674_ok : Node.check D_R11111 T2674 [((535/1024),(535/512)),((999/1024),(333/256)),((2997/1024),(1665/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2674_ok
def T2673 : Node := Node.leaf L2673
theorem T2673_ok : Node.check D_R11111 T2673 [((535/1024),(535/512)),((999/1024),(333/256)),((333/128),(2997/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2673_ok
def T2672 : Node := Node.split 2 T2673 T2674
theorem T2672_ok : Node.check D_R11111 T2672 [((535/1024),(535/512)),((999/1024),(333/256)),((333/128),(1665/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2673_ok T2674_ok
def T2671 : Node := Node.leaf L2671
theorem T2671_ok : Node.check D_R11111 T2671 [((535/1024),(535/512)),((333/512),(999/1024)),((333/128),(1665/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2671_ok
def T2670 : Node := Node.split 1 T2671 T2672
theorem T2670_ok : Node.check D_R11111 T2670 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2671_ok T2672_ok
def T2669 : Node := Node.split 3 T2670 T2675
theorem T2669_ok : Node.check D_R11111 T2669 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2670_ok T2675_ok
def T2668 : Node := Node.leaf L2668
theorem T2668_ok : Node.check D_R11111 T2668 [((0),(535/1024)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2668_ok
def T2667 : Node := Node.split 0 T2668 T2669
theorem T2667_ok : Node.check D_R11111 T2667 [((0),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2668_ok T2669_ok
def T2666 : Node := Node.split 2 T2667 T2676
theorem T2666_ok : Node.check D_R11111 T2666 [((0),(535/512)),((333/512),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2667_ok T2676_ok
def T2665 : Node := Node.leaf L2665
theorem T2665_ok : Node.check D_R11111 T2665 [((0),(535/512)),((0),(333/512)),((333/128),(999/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2665_ok
def T2664 : Node := Node.split 1 T2665 T2666
theorem T2664_ok : Node.check D_R11111 T2664 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2665_ok T2666_ok
def T2663 : Node := Node.leaf L2663
theorem T2663_ok : Node.check D_R11111 T2663 [((535/1024),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2663_ok
def T2662 : Node := Node.leaf L2662
theorem T2662_ok : Node.check D_R11111 T2662 [((535/1024),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2662_ok
def T2661 : Node := Node.split 3 T2662 T2663
theorem T2661_ok : Node.check D_R11111 T2661 [((535/1024),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2662_ok T2663_ok
def T2660 : Node := Node.leaf L2660
theorem T2660_ok : Node.check D_R11111 T2660 [((0),(535/1024)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2660_ok
def T2659 : Node := Node.split 0 T2660 T2661
theorem T2659_ok : Node.check D_R11111 T2659 [((0),(535/512)),((333/512),(333/256)),((1665/512),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2660_ok T2661_ok
def T2658 : Node := Node.leaf L2658
theorem T2658_ok : Node.check D_R11111 T2658 [((535/1024),(535/512)),((999/1024),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2658_ok
def T2657 : Node := Node.leaf L2657
theorem T2657_ok : Node.check D_R11111 T2657 [((535/1024),(535/512)),((333/512),(999/1024)),((333/128),(1665/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2657_ok
def T2656 : Node := Node.split 1 T2657 T2658
theorem T2656_ok : Node.check D_R11111 T2656 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2657_ok T2658_ok
def T2655 : Node := Node.leaf L2655
theorem T2655_ok : Node.check D_R11111 T2655 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2655_ok
def T2654 : Node := Node.split 3 T2655 T2656
theorem T2654_ok : Node.check D_R11111 T2654 [((535/1024),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2655_ok T2656_ok
def T2653 : Node := Node.leaf L2653
theorem T2653_ok : Node.check D_R11111 T2653 [((0),(535/1024)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2653_ok
def T2652 : Node := Node.split 0 T2653 T2654
theorem T2652_ok : Node.check D_R11111 T2652 [((0),(535/512)),((333/512),(333/256)),((333/128),(1665/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2653_ok T2654_ok
def T2651 : Node := Node.split 2 T2652 T2659
theorem T2651_ok : Node.check D_R11111 T2651 [((0),(535/512)),((333/512),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2652_ok T2659_ok
def T2650 : Node := Node.leaf L2650
theorem T2650_ok : Node.check D_R11111 T2650 [((0),(535/512)),((0),(333/512)),((333/128),(999/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2650_ok
def T2649 : Node := Node.split 1 T2650 T2651
theorem T2649_ok : Node.check D_R11111 T2649 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2650_ok T2651_ok
def T2648 : Node := Node.split 3 T2649 T2664
theorem T2648_ok : Node.check D_R11111 T2648 [((0),(535/512)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2649_ok T2664_ok
def T2647 : Node := Node.split 0 T2648 T2679
theorem T2647_ok : Node.check D_R11111 T2647 [((0),(535/256)),((0),(333/256)),((333/128),(999/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2648_ok T2679_ok
def T2646 : Node := Node.split 2 T2647 T2714
theorem T2646_ok : Node.check D_R11111 T2646 [((0),(535/256)),((0),(333/256)),((333/128),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2647_ok T2714_ok
def T2645 : Node := Node.split 1 T2646 T2747
theorem T2645_ok : Node.check D_R11111 T2645 [((0),(535/256)),((0),(333/128)),((333/128),(333/64)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2646_ok T2747_ok
def T2644 : Node := Node.split 3 T2645 T2790
theorem T2644_ok : Node.check D_R11111 T2644 [((0),(535/256)),((0),(333/128)),((333/128),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2645_ok T2790_ok
def T2643 : Node := Node.split 0 T2644 T2815
theorem T2643_ok : Node.check D_R11111 T2643 [((0),(535/128)),((0),(333/128)),((333/128),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2644_ok T2815_ok
def T2642 : Node := Node.leaf L2642
theorem T2642_ok : Node.check D_R11111 T2642 [((535/256),(535/128)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(535/128))] = true := Node.check_leaf_of _ _ _ L2642_ok
def T2641 : Node := Node.leaf L2641
theorem T2641_ok : Node.check D_R11111 T2641 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2641_ok
def T2640 : Node := Node.leaf L2640
theorem T2640_ok : Node.check D_R11111 T2640 [((1605/512),(535/128)),((999/512),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2640_ok
def T2639 : Node := Node.leaf L2639
theorem T2639_ok : Node.check D_R11111 T2639 [((1605/512),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2639_ok
def T2638 : Node := Node.leaf L2638
theorem T2638_ok : Node.check D_R11111 T2638 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2638_ok
def T2637 : Node := Node.split 2 T2638 T2639
theorem T2637_ok : Node.check D_R11111 T2637 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2638_ok T2639_ok
def T2636 : Node := Node.split 1 T2637 T2640
theorem T2636_ok : Node.check D_R11111 T2636 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2637_ok T2640_ok
def T2635 : Node := Node.split 3 T2636 T2641
theorem T2635_ok : Node.check D_R11111 T2635 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2636_ok T2641_ok
def T2634 : Node := Node.leaf L2634
theorem T2634_ok : Node.check D_R11111 T2634 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2634_ok
def T2633 : Node := Node.leaf L2633
theorem T2633_ok : Node.check D_R11111 T2633 [((535/256),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2633_ok
def T2632 : Node := Node.leaf L2632
theorem T2632_ok : Node.check D_R11111 T2632 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2632_ok
def T2631 : Node := Node.split 2 T2632 T2633
theorem T2631_ok : Node.check D_R11111 T2631 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2632_ok T2633_ok
def T2630 : Node := Node.split 1 T2631 T2634
theorem T2630_ok : Node.check D_R11111 T2630 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2631_ok T2634_ok
def T2629 : Node := Node.leaf L2629
theorem T2629_ok : Node.check D_R11111 T2629 [((535/256),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2629_ok
def T2628 : Node := Node.leaf L2628
theorem T2628_ok : Node.check D_R11111 T2628 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2628_ok
def T2627 : Node := Node.split 2 T2628 T2629
theorem T2627_ok : Node.check D_R11111 T2627 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2628_ok T2629_ok
def T2626 : Node := Node.leaf L2626
theorem T2626_ok : Node.check D_R11111 T2626 [((535/256),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2626_ok
def T2625 : Node := Node.leaf L2625
theorem T2625_ok : Node.check D_R11111 T2625 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2625_ok
def T2624 : Node := Node.split 2 T2625 T2626
theorem T2624_ok : Node.check D_R11111 T2624 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2625_ok T2626_ok
def T2623 : Node := Node.split 1 T2624 T2627
theorem T2623_ok : Node.check D_R11111 T2623 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2624_ok T2627_ok
def T2622 : Node := Node.split 3 T2623 T2630
theorem T2622_ok : Node.check D_R11111 T2622 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2623_ok T2630_ok
def T2621 : Node := Node.split 0 T2622 T2635
theorem T2621_ok : Node.check D_R11111 T2621 [((535/256),(535/128)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2622_ok T2635_ok
def T2620 : Node := Node.split 2 T2621 T2642
theorem T2620_ok : Node.check D_R11111 T2620 [((535/256),(535/128)),((333/256),(333/128)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2621_ok T2642_ok
def T2619 : Node := Node.leaf L2619
theorem T2619_ok : Node.check D_R11111 T2619 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2619_ok
def T2618 : Node := Node.leaf L2618
theorem T2618_ok : Node.check D_R11111 T2618 [((1605/512),(535/128)),((333/512),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2618_ok
def T2617 : Node := Node.leaf L2617
theorem T2617_ok : Node.check D_R11111 T2617 [((1605/512),(535/128)),((0),(333/512)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2617_ok
def T2616 : Node := Node.split 1 T2617 T2618
theorem T2616_ok : Node.check D_R11111 T2616 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2617_ok T2618_ok
def T2615 : Node := Node.split 3 T2616 T2619
theorem T2615_ok : Node.check D_R11111 T2615 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2616_ok T2619_ok
def T2614 : Node := Node.leaf L2614
theorem T2614_ok : Node.check D_R11111 T2614 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2614_ok
def T2613 : Node := Node.leaf L2613
theorem T2613_ok : Node.check D_R11111 T2613 [((535/256),(1605/512)),((0),(333/512)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2613_ok
def T2612 : Node := Node.split 1 T2613 T2614
theorem T2612_ok : Node.check D_R11111 T2612 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2613_ok T2614_ok
def T2611 : Node := Node.leaf L2611
theorem T2611_ok : Node.check D_R11111 T2611 [((535/256),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2611_ok
def T2610 : Node := Node.leaf L2610
theorem T2610_ok : Node.check D_R11111 T2610 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2610_ok
def T2609 : Node := Node.split 2 T2610 T2611
theorem T2609_ok : Node.check D_R11111 T2609 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2610_ok T2611_ok
def T2608 : Node := Node.leaf L2608
theorem T2608_ok : Node.check D_R11111 T2608 [((535/256),(1605/512)),((0),(333/512)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2608_ok
def T2607 : Node := Node.split 1 T2608 T2609
theorem T2607_ok : Node.check D_R11111 T2607 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2608_ok T2609_ok
def T2606 : Node := Node.split 3 T2607 T2612
theorem T2606_ok : Node.check D_R11111 T2606 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2607_ok T2612_ok
def T2605 : Node := Node.split 0 T2606 T2615
theorem T2605_ok : Node.check D_R11111 T2605 [((535/256),(535/128)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2606_ok T2615_ok
def T2604 : Node := Node.leaf L2604
theorem T2604_ok : Node.check D_R11111 T2604 [((1605/512),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2604_ok
def T2603 : Node := Node.leaf L2603
theorem T2603_ok : Node.check D_R11111 T2603 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2603_ok
def T2602 : Node := Node.split 2 T2603 T2604
theorem T2602_ok : Node.check D_R11111 T2602 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2603_ok T2604_ok
def T2601 : Node := Node.leaf L2601
theorem T2601_ok : Node.check D_R11111 T2601 [((1605/512),(535/128)),((0),(333/512)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2601_ok
def T2600 : Node := Node.split 1 T2601 T2602
theorem T2600_ok : Node.check D_R11111 T2600 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2601_ok T2602_ok
def T2599 : Node := Node.leaf L2599
theorem T2599_ok : Node.check D_R11111 T2599 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2599_ok
def T2598 : Node := Node.leaf L2598
theorem T2598_ok : Node.check D_R11111 T2598 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L2598_ok
def T2597 : Node := Node.leaf L2597
theorem T2597_ok : Node.check D_R11111 T2597 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2597_ok
def T2596 : Node := Node.split 3 T2597 T2598
theorem T2596_ok : Node.check D_R11111 T2596 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2597_ok T2598_ok
def T2595 : Node := Node.split 0 T2596 T2599
theorem T2595_ok : Node.check D_R11111 T2595 [((1605/512),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2596_ok T2599_ok
def T2594 : Node := Node.leaf L2594
theorem T2594_ok : Node.check D_R11111 T2594 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2594_ok
def T2593 : Node := Node.split 2 T2594 T2595
theorem T2593_ok : Node.check D_R11111 T2593 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2594_ok T2595_ok
def T2592 : Node := Node.leaf L2592
theorem T2592_ok : Node.check D_R11111 T2592 [((1605/512),(535/128)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2592_ok
def T2591 : Node := Node.split 1 T2592 T2593
theorem T2591_ok : Node.check D_R11111 T2591 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2592_ok T2593_ok
def T2590 : Node := Node.split 3 T2591 T2600
theorem T2590_ok : Node.check D_R11111 T2590 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2591_ok T2600_ok
def T2589 : Node := Node.leaf L2589
theorem T2589_ok : Node.check D_R11111 T2589 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2589_ok
def T2588 : Node := Node.leaf L2588
theorem T2588_ok : Node.check D_R11111 T2588 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L2588_ok
def T2587 : Node := Node.leaf L2587
theorem T2587_ok : Node.check D_R11111 T2587 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L2587_ok
def T2586 : Node := Node.split 3 T2587 T2588
theorem T2586_ok : Node.check D_R11111 T2586 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2587_ok T2588_ok
def T2585 : Node := Node.split 0 T2586 T2589
theorem T2585_ok : Node.check D_R11111 T2585 [((535/256),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2586_ok T2589_ok
def T2584 : Node := Node.leaf L2584
theorem T2584_ok : Node.check D_R11111 T2584 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2584_ok
def T2583 : Node := Node.split 2 T2584 T2585
theorem T2583_ok : Node.check D_R11111 T2583 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2584_ok T2585_ok
def T2582 : Node := Node.leaf L2582
theorem T2582_ok : Node.check D_R11111 T2582 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L2582_ok
def T2581 : Node := Node.split 1 T2582 T2583
theorem T2581_ok : Node.check D_R11111 T2581 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2582_ok T2583_ok
def T2580 : Node := Node.leaf L2580
theorem T2580_ok : Node.check D_R11111 T2580 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L2580_ok
def T2579 : Node := Node.leaf L2579
theorem T2579_ok : Node.check D_R11111 T2579 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2579_ok
def T2578 : Node := Node.leaf L2578
theorem T2578_ok : Node.check D_R11111 T2578 [((5885/2048),(1605/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2578_ok
def T2577 : Node := Node.leaf L2577
theorem T2577_ok : Node.check D_R11111 T2577 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2577_ok
def T2576 : Node := Node.split 1 T2577 T2578
theorem T2576_ok : Node.check D_R11111 T2576 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2577_ok T2578_ok
def T2575 : Node := Node.split 3 T2576 T2579
theorem T2575_ok : Node.check D_R11111 T2575 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2576_ok T2579_ok
def T2574 : Node := Node.leaf L2574
theorem T2574_ok : Node.check D_R11111 T2574 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2574_ok
def T2573 : Node := Node.split 0 T2574 T2575
theorem T2573_ok : Node.check D_R11111 T2573 [((2675/1024),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2574_ok T2575_ok
def T2572 : Node := Node.leaf L2572
theorem T2572_ok : Node.check D_R11111 T2572 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2572_ok
def T2571 : Node := Node.split 2 T2572 T2573
theorem T2571_ok : Node.check D_R11111 T2571 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2572_ok T2573_ok
def T2570 : Node := Node.leaf L2570
theorem T2570_ok : Node.check D_R11111 T2570 [((2675/1024),(1605/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2570_ok
def T2569 : Node := Node.split 1 T2570 T2571
theorem T2569_ok : Node.check D_R11111 T2569 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2570_ok T2571_ok
def T2568 : Node := Node.split 3 T2569 T2580
theorem T2568_ok : Node.check D_R11111 T2568 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2569_ok T2580_ok
def T2567 : Node := Node.leaf L2567
theorem T2567_ok : Node.check D_R11111 T2567 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L2567_ok
def T2566 : Node := Node.leaf L2566
theorem T2566_ok : Node.check D_R11111 T2566 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L2566_ok
def T2565 : Node := Node.leaf L2565
theorem T2565_ok : Node.check D_R11111 T2565 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L2565_ok
def T2564 : Node := Node.split 1 T2565 T2566
theorem T2564_ok : Node.check D_R11111 T2564 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2565_ok T2566_ok
def T2563 : Node := Node.leaf L2563
theorem T2563_ok : Node.check D_R11111 T2563 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L2563_ok
def T2562 : Node := Node.split 3 T2563 T2564
theorem T2562_ok : Node.check D_R11111 T2562 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2563_ok T2564_ok
def T2561 : Node := Node.split 0 T2562 T2567
theorem T2561_ok : Node.check D_R11111 T2561 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2562_ok T2567_ok
def T2560 : Node := Node.leaf L2560
theorem T2560_ok : Node.check D_R11111 T2560 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L2560_ok
def T2559 : Node := Node.split 2 T2560 T2561
theorem T2559_ok : Node.check D_R11111 T2559 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2560_ok T2561_ok
def T2558 : Node := Node.leaf L2558
theorem T2558_ok : Node.check D_R11111 T2558 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L2558_ok
def T2557 : Node := Node.split 1 T2558 T2559
theorem T2557_ok : Node.check D_R11111 T2557 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2558_ok T2559_ok
def T2556 : Node := Node.leaf L2556
theorem T2556_ok : Node.check D_R11111 T2556 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2556_ok
def T2555 : Node := Node.leaf L2555
theorem T2555_ok : Node.check D_R11111 T2555 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2555_ok
def T2554 : Node := Node.leaf L2554
theorem T2554_ok : Node.check D_R11111 T2554 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2554_ok
def T2553 : Node := Node.leaf L2553
theorem T2553_ok : Node.check D_R11111 T2553 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2553_ok
def T2552 : Node := Node.leaf L2552
theorem T2552_ok : Node.check D_R11111 T2552 [((9095/4096),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2552_ok
def T2551 : Node := Node.leaf L2551
theorem T2551_ok : Node.check D_R11111 T2551 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L2551_ok
def T2550 : Node := Node.leaf L2550
theorem T2550_ok : Node.check D_R11111 T2550 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L2550_ok
def T2549 : Node := Node.leaf L2549
theorem T2549_ok : Node.check D_R11111 T2549 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L2549_ok
def T2548 : Node := Node.split 1 T2549 T2550
theorem T2548_ok : Node.check D_R11111 T2548 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2549_ok T2550_ok
def T2547 : Node := Node.split 3 T2548 T2551
theorem T2547_ok : Node.check D_R11111 T2547 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2548_ok T2551_ok
def T2546 : Node := Node.split 0 T2547 T2552
theorem T2546_ok : Node.check D_R11111 T2546 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2547_ok T2552_ok
def T2545 : Node := Node.split 2 T2546 T2553
theorem T2545_ok : Node.check D_R11111 T2545 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2546_ok T2553_ok
def T2544 : Node := Node.split 1 T2545 T2554
theorem T2544_ok : Node.check D_R11111 T2544 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2545_ok T2554_ok
def T2543 : Node := Node.split 3 T2544 T2555
theorem T2543_ok : Node.check D_R11111 T2543 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2544_ok T2555_ok
def T2542 : Node := Node.split 0 T2543 T2556
theorem T2542_ok : Node.check D_R11111 T2542 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2543_ok T2556_ok
def T2541 : Node := Node.leaf L2541
theorem T2541_ok : Node.check D_R11111 T2541 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2541_ok
def T2540 : Node := Node.split 2 T2541 T2542
theorem T2540_ok : Node.check D_R11111 T2540 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2541_ok T2542_ok
def T2539 : Node := Node.leaf L2539
theorem T2539_ok : Node.check D_R11111 T2539 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L2539_ok
def T2538 : Node := Node.split 1 T2539 T2540
theorem T2538_ok : Node.check D_R11111 T2538 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2539_ok T2540_ok
def T2537 : Node := Node.split 3 T2538 T2557
theorem T2537_ok : Node.check D_R11111 T2537 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2538_ok T2557_ok
def T2536 : Node := Node.split 0 T2537 T2568
theorem T2536_ok : Node.check D_R11111 T2536 [((535/256),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2537_ok T2568_ok
def T2535 : Node := Node.leaf L2535
theorem T2535_ok : Node.check D_R11111 T2535 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2535_ok
def T2534 : Node := Node.split 2 T2535 T2536
theorem T2534_ok : Node.check D_R11111 T2534 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2535_ok T2536_ok
def T2533 : Node := Node.leaf L2533
theorem T2533_ok : Node.check D_R11111 T2533 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L2533_ok
def T2532 : Node := Node.split 1 T2533 T2534
theorem T2532_ok : Node.check D_R11111 T2532 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2533_ok T2534_ok
def T2531 : Node := Node.split 3 T2532 T2581
theorem T2531_ok : Node.check D_R11111 T2531 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2532_ok T2581_ok
def T2530 : Node := Node.split 0 T2531 T2590
theorem T2530_ok : Node.check D_R11111 T2530 [((535/256),(535/128)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2531_ok T2590_ok
def T2529 : Node := Node.split 2 T2530 T2605
theorem T2529_ok : Node.check D_R11111 T2529 [((535/256),(535/128)),((0),(333/256)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2530_ok T2605_ok
def T2528 : Node := Node.split 1 T2529 T2620
theorem T2528_ok : Node.check D_R11111 T2528 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2529_ok T2620_ok
def T2527 : Node := Node.leaf L2527
theorem T2527_ok : Node.check D_R11111 T2527 [((1605/512),(535/128)),((333/256),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2527_ok
def T2526 : Node := Node.leaf L2526
theorem T2526_ok : Node.check D_R11111 T2526 [((1605/512),(535/128)),((999/512),(333/128)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2526_ok
def T2525 : Node := Node.leaf L2525
theorem T2525_ok : Node.check D_R11111 T2525 [((1605/512),(535/128)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2525_ok
def T2524 : Node := Node.leaf L2524
theorem T2524_ok : Node.check D_R11111 T2524 [((3745/1024),(535/128)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2524_ok
def T2523 : Node := Node.leaf L2523
theorem T2523_ok : Node.check D_R11111 T2523 [((3745/1024),(535/128)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2523_ok
def T2522 : Node := Node.split 3 T2523 T2524
theorem T2522_ok : Node.check D_R11111 T2522 [((3745/1024),(535/128)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2523_ok T2524_ok
def T2521 : Node := Node.leaf L2521
theorem T2521_ok : Node.check D_R11111 T2521 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2521_ok
def T2520 : Node := Node.leaf L2520
theorem T2520_ok : Node.check D_R11111 T2520 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2520_ok
def T2519 : Node := Node.split 3 T2520 T2521
theorem T2519_ok : Node.check D_R11111 T2519 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2520_ok T2521_ok
def T2518 : Node := Node.split 0 T2519 T2522
theorem T2518_ok : Node.check D_R11111 T2518 [((1605/512),(535/128)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2519_ok T2522_ok
def T2517 : Node := Node.split 2 T2518 T2525
theorem T2517_ok : Node.check D_R11111 T2517 [((1605/512),(535/128)),((333/256),(999/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2518_ok T2525_ok
def T2516 : Node := Node.split 1 T2517 T2526
theorem T2516_ok : Node.check D_R11111 T2516 [((1605/512),(535/128)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2517_ok T2526_ok
def T2515 : Node := Node.split 3 T2516 T2527
theorem T2515_ok : Node.check D_R11111 T2515 [((1605/512),(535/128)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2516_ok T2527_ok
def T2514 : Node := Node.leaf L2514
theorem T2514_ok : Node.check D_R11111 T2514 [((535/256),(1605/512)),((999/512),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2514_ok
def T2513 : Node := Node.leaf L2513
theorem T2513_ok : Node.check D_R11111 T2513 [((535/256),(1605/512)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2513_ok
def T2512 : Node := Node.leaf L2512
theorem T2512_ok : Node.check D_R11111 T2512 [((535/256),(1605/512)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2512_ok
def T2511 : Node := Node.split 2 T2512 T2513
theorem T2511_ok : Node.check D_R11111 T2511 [((535/256),(1605/512)),((333/256),(999/512)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2512_ok T2513_ok
def T2510 : Node := Node.split 1 T2511 T2514
theorem T2510_ok : Node.check D_R11111 T2510 [((535/256),(1605/512)),((333/256),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2511_ok T2514_ok
def T2509 : Node := Node.leaf L2509
theorem T2509_ok : Node.check D_R11111 T2509 [((535/256),(1605/512)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2509_ok
def T2508 : Node := Node.leaf L2508
theorem T2508_ok : Node.check D_R11111 T2508 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2508_ok
def T2507 : Node := Node.leaf L2507
theorem T2507_ok : Node.check D_R11111 T2507 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2507_ok
def T2506 : Node := Node.split 3 T2507 T2508
theorem T2506_ok : Node.check D_R11111 T2506 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2507_ok T2508_ok
def T2505 : Node := Node.leaf L2505
theorem T2505_ok : Node.check D_R11111 T2505 [((535/256),(2675/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2505_ok
def T2504 : Node := Node.leaf L2504
theorem T2504_ok : Node.check D_R11111 T2504 [((535/256),(2675/1024)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2504_ok
def T2503 : Node := Node.split 3 T2504 T2505
theorem T2503_ok : Node.check D_R11111 T2503 [((535/256),(2675/1024)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2504_ok T2505_ok
def T2502 : Node := Node.split 0 T2503 T2506
theorem T2502_ok : Node.check D_R11111 T2502 [((535/256),(1605/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2503_ok T2506_ok
def T2501 : Node := Node.split 2 T2502 T2509
theorem T2501_ok : Node.check D_R11111 T2501 [((535/256),(1605/512)),((999/512),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2502_ok T2509_ok
def T2500 : Node := Node.leaf L2500
theorem T2500_ok : Node.check D_R11111 T2500 [((2675/1024),(1605/512)),((333/256),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2500_ok
def T2499 : Node := Node.leaf L2499
theorem T2499_ok : Node.check D_R11111 T2499 [((2675/1024),(1605/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2499_ok
def T2498 : Node := Node.split 3 T2499 T2500
theorem T2498_ok : Node.check D_R11111 T2498 [((2675/1024),(1605/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2499_ok T2500_ok
def T2497 : Node := Node.leaf L2497
theorem T2497_ok : Node.check D_R11111 T2497 [((535/256),(2675/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2497_ok
def T2496 : Node := Node.leaf L2496
theorem T2496_ok : Node.check D_R11111 T2496 [((535/256),(2675/1024)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2496_ok
def T2495 : Node := Node.split 3 T2496 T2497
theorem T2495_ok : Node.check D_R11111 T2495 [((535/256),(2675/1024)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2496_ok T2497_ok
def T2494 : Node := Node.split 0 T2495 T2498
theorem T2494_ok : Node.check D_R11111 T2494 [((535/256),(1605/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2495_ok T2498_ok
def T2493 : Node := Node.leaf L2493
theorem T2493_ok : Node.check D_R11111 T2493 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2493_ok
def T2492 : Node := Node.leaf L2492
theorem T2492_ok : Node.check D_R11111 T2492 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2492_ok
def T2491 : Node := Node.split 3 T2492 T2493
theorem T2491_ok : Node.check D_R11111 T2491 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2492_ok T2493_ok
def T2490 : Node := Node.leaf L2490
theorem T2490_ok : Node.check D_R11111 T2490 [((535/256),(2675/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2490_ok
def T2489 : Node := Node.leaf L2489
theorem T2489_ok : Node.check D_R11111 T2489 [((535/256),(2675/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2489_ok
def T2488 : Node := Node.split 3 T2489 T2490
theorem T2488_ok : Node.check D_R11111 T2488 [((535/256),(2675/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2489_ok T2490_ok
def T2487 : Node := Node.split 0 T2488 T2491
theorem T2487_ok : Node.check D_R11111 T2487 [((535/256),(1605/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2488_ok T2491_ok
def T2486 : Node := Node.split 2 T2487 T2494
theorem T2486_ok : Node.check D_R11111 T2486 [((535/256),(1605/512)),((333/256),(999/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2487_ok T2494_ok
def T2485 : Node := Node.split 1 T2486 T2501
theorem T2485_ok : Node.check D_R11111 T2485 [((535/256),(1605/512)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2486_ok T2501_ok
def T2484 : Node := Node.split 3 T2485 T2510
theorem T2484_ok : Node.check D_R11111 T2484 [((535/256),(1605/512)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2485_ok T2510_ok
def T2483 : Node := Node.split 0 T2484 T2515
theorem T2483_ok : Node.check D_R11111 T2483 [((535/256),(535/128)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2484_ok T2515_ok
def T2482 : Node := Node.leaf L2482
theorem T2482_ok : Node.check D_R11111 T2482 [((1605/512),(535/128)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2482_ok
def T2481 : Node := Node.leaf L2481
theorem T2481_ok : Node.check D_R11111 T2481 [((1605/512),(535/128)),((999/512),(333/128)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2481_ok
def T2480 : Node := Node.split 2 T2481 T2482
theorem T2480_ok : Node.check D_R11111 T2480 [((1605/512),(535/128)),((999/512),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2481_ok T2482_ok
def T2479 : Node := Node.leaf L2479
theorem T2479_ok : Node.check D_R11111 T2479 [((1605/512),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2479_ok
def T2478 : Node := Node.leaf L2478
theorem T2478_ok : Node.check D_R11111 T2478 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2478_ok
def T2477 : Node := Node.split 2 T2478 T2479
theorem T2477_ok : Node.check D_R11111 T2477 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2478_ok T2479_ok
def T2476 : Node := Node.split 1 T2477 T2480
theorem T2476_ok : Node.check D_R11111 T2476 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2477_ok T2480_ok
def T2475 : Node := Node.leaf L2475
theorem T2475_ok : Node.check D_R11111 T2475 [((3745/1024),(535/128)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2475_ok
def T2474 : Node := Node.leaf L2474
theorem T2474_ok : Node.check D_R11111 T2474 [((3745/1024),(535/128)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2474_ok
def T2473 : Node := Node.split 3 T2474 T2475
theorem T2473_ok : Node.check D_R11111 T2473 [((3745/1024),(535/128)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2474_ok T2475_ok
def T2472 : Node := Node.leaf L2472
theorem T2472_ok : Node.check D_R11111 T2472 [((1605/512),(3745/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2472_ok
def T2471 : Node := Node.leaf L2471
theorem T2471_ok : Node.check D_R11111 T2471 [((1605/512),(3745/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2471_ok
def T2470 : Node := Node.split 3 T2471 T2472
theorem T2470_ok : Node.check D_R11111 T2470 [((1605/512),(3745/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2471_ok T2472_ok
def T2469 : Node := Node.split 0 T2470 T2473
theorem T2469_ok : Node.check D_R11111 T2469 [((1605/512),(535/128)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2470_ok T2473_ok
def T2468 : Node := Node.leaf L2468
theorem T2468_ok : Node.check D_R11111 T2468 [((1605/512),(535/128)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2468_ok
def T2467 : Node := Node.split 2 T2468 T2469
theorem T2467_ok : Node.check D_R11111 T2467 [((1605/512),(535/128)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2468_ok T2469_ok
def T2466 : Node := Node.leaf L2466
theorem T2466_ok : Node.check D_R11111 T2466 [((3745/1024),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2466_ok
def T2465 : Node := Node.leaf L2465
theorem T2465_ok : Node.check D_R11111 T2465 [((3745/1024),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2465_ok
def T2464 : Node := Node.split 3 T2465 T2466
theorem T2464_ok : Node.check D_R11111 T2464 [((3745/1024),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2465_ok T2466_ok
def T2463 : Node := Node.leaf L2463
theorem T2463_ok : Node.check D_R11111 T2463 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2463_ok
def T2462 : Node := Node.leaf L2462
theorem T2462_ok : Node.check D_R11111 T2462 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2462_ok
def T2461 : Node := Node.split 3 T2462 T2463
theorem T2461_ok : Node.check D_R11111 T2461 [((1605/512),(3745/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2462_ok T2463_ok
def T2460 : Node := Node.split 0 T2461 T2464
theorem T2460_ok : Node.check D_R11111 T2460 [((1605/512),(535/128)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2461_ok T2464_ok
def T2459 : Node := Node.leaf L2459
theorem T2459_ok : Node.check D_R11111 T2459 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2459_ok
def T2458 : Node := Node.split 2 T2459 T2460
theorem T2458_ok : Node.check D_R11111 T2458 [((1605/512),(535/128)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2459_ok T2460_ok
def T2457 : Node := Node.split 1 T2458 T2467
theorem T2457_ok : Node.check D_R11111 T2457 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2458_ok T2467_ok
def T2456 : Node := Node.split 3 T2457 T2476
theorem T2456_ok : Node.check D_R11111 T2456 [((1605/512),(535/128)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2457_ok T2476_ok
def T2455 : Node := Node.leaf L2455
theorem T2455_ok : Node.check D_R11111 T2455 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2455_ok
def T2454 : Node := Node.leaf L2454
theorem T2454_ok : Node.check D_R11111 T2454 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2454_ok
def T2453 : Node := Node.leaf L2453
theorem T2453_ok : Node.check D_R11111 T2453 [((535/256),(2675/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2453_ok
def T2452 : Node := Node.leaf L2452
theorem T2452_ok : Node.check D_R11111 T2452 [((4815/2048),(2675/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2452_ok
def T2451 : Node := Node.leaf L2451
theorem T2451_ok : Node.check D_R11111 T2451 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2451_ok
def T2450 : Node := Node.leaf L2450
theorem T2450_ok : Node.check D_R11111 T2450 [((535/256),(4815/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2450_ok
def T2449 : Node := Node.leaf L2449
theorem T2449_ok : Node.check D_R11111 T2449 [((535/256),(4815/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2449_ok
def T2448 : Node := Node.leaf L2448
theorem T2448_ok : Node.check D_R11111 T2448 [((9095/4096),(4815/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2448_ok
def T2447 : Node := Node.leaf L2447
theorem T2447_ok : Node.check D_R11111 T2447 [((535/256),(9095/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2447_ok
def T2446 : Node := Node.leaf L2446
theorem T2446_ok : Node.check D_R11111 T2446 [((535/256),(9095/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2446_ok
def T2445 : Node := Node.leaf L2445
theorem T2445_ok : Node.check D_R11111 T2445 [((535/256),(9095/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2445_ok
def T2444 : Node := Node.leaf L2444
theorem T2444_ok : Node.check D_R11111 T2444 [((535/256),(9095/4096)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2444_ok
def T2443 : Node := Node.split 2 T2444 T2445
theorem T2443_ok : Node.check D_R11111 T2443 [((535/256),(9095/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2444_ok T2445_ok
def T2442 : Node := Node.split 1 T2443 T2446
theorem T2442_ok : Node.check D_R11111 T2442 [((535/256),(9095/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2443_ok T2446_ok
def T2441 : Node := Node.split 3 T2442 T2447
theorem T2441_ok : Node.check D_R11111 T2441 [((535/256),(9095/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2442_ok T2447_ok
def T2440 : Node := Node.split 0 T2441 T2448
theorem T2440_ok : Node.check D_R11111 T2440 [((535/256),(4815/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2441_ok T2448_ok
def T2439 : Node := Node.split 2 T2440 T2449
theorem T2439_ok : Node.check D_R11111 T2439 [((535/256),(4815/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2440_ok T2449_ok
def T2438 : Node := Node.split 1 T2439 T2450
theorem T2438_ok : Node.check D_R11111 T2438 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2439_ok T2450_ok
def T2437 : Node := Node.split 3 T2438 T2451
theorem T2437_ok : Node.check D_R11111 T2437 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2438_ok T2451_ok
def T2436 : Node := Node.split 0 T2437 T2452
theorem T2436_ok : Node.check D_R11111 T2436 [((535/256),(2675/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2437_ok T2452_ok
def T2435 : Node := Node.leaf L2435
theorem T2435_ok : Node.check D_R11111 T2435 [((535/256),(2675/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2435_ok
def T2434 : Node := Node.split 2 T2435 T2436
theorem T2434_ok : Node.check D_R11111 T2434 [((535/256),(2675/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2435_ok T2436_ok
def T2433 : Node := Node.split 1 T2434 T2453
theorem T2433_ok : Node.check D_R11111 T2433 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2434_ok T2453_ok
def T2432 : Node := Node.split 3 T2433 T2454
theorem T2432_ok : Node.check D_R11111 T2432 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2433_ok T2454_ok
def T2431 : Node := Node.split 0 T2432 T2455
theorem T2431_ok : Node.check D_R11111 T2431 [((535/256),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2432_ok T2455_ok
def T2430 : Node := Node.leaf L2430
theorem T2430_ok : Node.check D_R11111 T2430 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2430_ok
def T2429 : Node := Node.split 2 T2430 T2431
theorem T2429_ok : Node.check D_R11111 T2429 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2430_ok T2431_ok
def T2428 : Node := Node.leaf L2428
theorem T2428_ok : Node.check D_R11111 T2428 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2428_ok
def T2427 : Node := Node.leaf L2427
theorem T2427_ok : Node.check D_R11111 T2427 [((2675/1024),(1605/512)),((1665/1024),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2427_ok
def T2426 : Node := Node.leaf L2426
theorem T2426_ok : Node.check D_R11111 T2426 [((2675/1024),(1605/512)),((333/256),(1665/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2426_ok
def T2425 : Node := Node.split 1 T2426 T2427
theorem T2425_ok : Node.check D_R11111 T2425 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2426_ok T2427_ok
def T2424 : Node := Node.split 3 T2425 T2428
theorem T2424_ok : Node.check D_R11111 T2424 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2425_ok T2428_ok
def T2423 : Node := Node.leaf L2423
theorem T2423_ok : Node.check D_R11111 T2423 [((535/256),(2675/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2423_ok
def T2422 : Node := Node.leaf L2422
theorem T2422_ok : Node.check D_R11111 T2422 [((535/256),(2675/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2422_ok
def T2421 : Node := Node.split 1 T2422 T2423
theorem T2421_ok : Node.check D_R11111 T2421 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2422_ok T2423_ok
def T2420 : Node := Node.leaf L2420
theorem T2420_ok : Node.check D_R11111 T2420 [((4815/2048),(2675/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2420_ok
def T2419 : Node := Node.leaf L2419
theorem T2419_ok : Node.check D_R11111 T2419 [((535/256),(4815/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2419_ok
def T2418 : Node := Node.leaf L2418
theorem T2418_ok : Node.check D_R11111 T2418 [((535/256),(4815/2048)),((3663/2048),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2418_ok
def T2417 : Node := Node.leaf L2417
theorem T2417_ok : Node.check D_R11111 T2417 [((535/256),(4815/2048)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2417_ok
def T2416 : Node := Node.split 1 T2417 T2418
theorem T2416_ok : Node.check D_R11111 T2416 [((535/256),(4815/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2417_ok T2418_ok
def T2415 : Node := Node.split 3 T2416 T2419
theorem T2415_ok : Node.check D_R11111 T2415 [((535/256),(4815/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2416_ok T2419_ok
def T2414 : Node := Node.split 0 T2415 T2420
theorem T2414_ok : Node.check D_R11111 T2414 [((535/256),(2675/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2415_ok T2420_ok
def T2413 : Node := Node.leaf L2413
theorem T2413_ok : Node.check D_R11111 T2413 [((535/256),(2675/1024)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2413_ok
def T2412 : Node := Node.split 2 T2413 T2414
theorem T2412_ok : Node.check D_R11111 T2412 [((535/256),(2675/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2413_ok T2414_ok
def T2411 : Node := Node.leaf L2411
theorem T2411_ok : Node.check D_R11111 T2411 [((535/256),(2675/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2411_ok
def T2410 : Node := Node.split 1 T2411 T2412
theorem T2410_ok : Node.check D_R11111 T2410 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2411_ok T2412_ok
def T2409 : Node := Node.split 3 T2410 T2421
theorem T2409_ok : Node.check D_R11111 T2409 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2410_ok T2421_ok
def T2408 : Node := Node.split 0 T2409 T2424
theorem T2408_ok : Node.check D_R11111 T2408 [((535/256),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2409_ok T2424_ok
def T2407 : Node := Node.leaf L2407
theorem T2407_ok : Node.check D_R11111 T2407 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2407_ok
def T2406 : Node := Node.split 2 T2407 T2408
theorem T2406_ok : Node.check D_R11111 T2406 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2407_ok T2408_ok
def T2405 : Node := Node.split 1 T2406 T2429
theorem T2405_ok : Node.check D_R11111 T2405 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2406_ok T2429_ok
def T2404 : Node := Node.leaf L2404
theorem T2404_ok : Node.check D_R11111 T2404 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2404_ok
def T2403 : Node := Node.leaf L2403
theorem T2403_ok : Node.check D_R11111 T2403 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2403_ok
def T2402 : Node := Node.split 3 T2403 T2404
theorem T2402_ok : Node.check D_R11111 T2402 [((2675/1024),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2403_ok T2404_ok
def T2401 : Node := Node.leaf L2401
theorem T2401_ok : Node.check D_R11111 T2401 [((535/256),(2675/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2401_ok
def T2400 : Node := Node.leaf L2400
theorem T2400_ok : Node.check D_R11111 T2400 [((4815/2048),(2675/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2400_ok
def T2399 : Node := Node.leaf L2399
theorem T2399_ok : Node.check D_R11111 T2399 [((535/256),(4815/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2399_ok
def T2398 : Node := Node.leaf L2398
theorem T2398_ok : Node.check D_R11111 T2398 [((535/256),(4815/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2398_ok
def T2397 : Node := Node.leaf L2397
theorem T2397_ok : Node.check D_R11111 T2397 [((535/256),(4815/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2397_ok
def T2396 : Node := Node.split 2 T2397 T2398
theorem T2396_ok : Node.check D_R11111 T2396 [((535/256),(4815/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2397_ok T2398_ok
def T2395 : Node := Node.split 1 T2396 T2399
theorem T2395_ok : Node.check D_R11111 T2395 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2396_ok T2399_ok
def T2394 : Node := Node.leaf L2394
theorem T2394_ok : Node.check D_R11111 T2394 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2394_ok
def T2393 : Node := Node.split 3 T2394 T2395
theorem T2393_ok : Node.check D_R11111 T2393 [((535/256),(4815/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2394_ok T2395_ok
def T2392 : Node := Node.split 0 T2393 T2400
theorem T2392_ok : Node.check D_R11111 T2392 [((535/256),(2675/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2393_ok T2400_ok
def T2391 : Node := Node.leaf L2391
theorem T2391_ok : Node.check D_R11111 T2391 [((535/256),(2675/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2391_ok
def T2390 : Node := Node.split 2 T2391 T2392
theorem T2390_ok : Node.check D_R11111 T2390 [((535/256),(2675/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2391_ok T2392_ok
def T2389 : Node := Node.split 1 T2390 T2401
theorem T2389_ok : Node.check D_R11111 T2389 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2390_ok T2401_ok
def T2388 : Node := Node.leaf L2388
theorem T2388_ok : Node.check D_R11111 T2388 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2388_ok
def T2387 : Node := Node.split 3 T2388 T2389
theorem T2387_ok : Node.check D_R11111 T2387 [((535/256),(2675/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2388_ok T2389_ok
def T2386 : Node := Node.split 0 T2387 T2402
theorem T2386_ok : Node.check D_R11111 T2386 [((535/256),(1605/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2387_ok T2402_ok
def T2385 : Node := Node.leaf L2385
theorem T2385_ok : Node.check D_R11111 T2385 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2385_ok
def T2384 : Node := Node.split 2 T2385 T2386
theorem T2384_ok : Node.check D_R11111 T2384 [((535/256),(1605/512)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2385_ok T2386_ok
def T2383 : Node := Node.leaf L2383
theorem T2383_ok : Node.check D_R11111 T2383 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2383_ok
def T2382 : Node := Node.leaf L2382
theorem T2382_ok : Node.check D_R11111 T2382 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2382_ok
def T2381 : Node := Node.split 3 T2382 T2383
theorem T2381_ok : Node.check D_R11111 T2381 [((2675/1024),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2382_ok T2383_ok
def T2380 : Node := Node.leaf L2380
theorem T2380_ok : Node.check D_R11111 T2380 [((535/256),(2675/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2380_ok
def T2379 : Node := Node.leaf L2379
theorem T2379_ok : Node.check D_R11111 T2379 [((535/256),(2675/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2379_ok
def T2378 : Node := Node.split 1 T2379 T2380
theorem T2378_ok : Node.check D_R11111 T2378 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2379_ok T2380_ok
def T2377 : Node := Node.leaf L2377
theorem T2377_ok : Node.check D_R11111 T2377 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2377_ok
def T2376 : Node := Node.split 3 T2377 T2378
theorem T2376_ok : Node.check D_R11111 T2376 [((535/256),(2675/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2377_ok T2378_ok
def T2375 : Node := Node.split 0 T2376 T2381
theorem T2375_ok : Node.check D_R11111 T2375 [((535/256),(1605/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2376_ok T2381_ok
def T2374 : Node := Node.leaf L2374
theorem T2374_ok : Node.check D_R11111 T2374 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2374_ok
def T2373 : Node := Node.split 2 T2374 T2375
theorem T2373_ok : Node.check D_R11111 T2373 [((535/256),(1605/512)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2374_ok T2375_ok
def T2372 : Node := Node.split 1 T2373 T2384
theorem T2372_ok : Node.check D_R11111 T2372 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2373_ok T2384_ok
def T2371 : Node := Node.split 3 T2372 T2405
theorem T2371_ok : Node.check D_R11111 T2371 [((535/256),(1605/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2372_ok T2405_ok
def T2370 : Node := Node.split 0 T2371 T2456
theorem T2370_ok : Node.check D_R11111 T2370 [((535/256),(535/128)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2371_ok T2456_ok
def T2369 : Node := Node.split 2 T2370 T2483
theorem T2369_ok : Node.check D_R11111 T2369 [((535/256),(535/128)),((333/256),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2370_ok T2483_ok
def T2368 : Node := Node.leaf L2368
theorem T2368_ok : Node.check D_R11111 T2368 [((1605/512),(535/128)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2368_ok
def T2367 : Node := Node.leaf L2367
theorem T2367_ok : Node.check D_R11111 T2367 [((1605/512),(535/128)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2367_ok
def T2366 : Node := Node.split 2 T2367 T2368
theorem T2366_ok : Node.check D_R11111 T2366 [((1605/512),(535/128)),((333/512),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2367_ok T2368_ok
def T2365 : Node := Node.leaf L2365
theorem T2365_ok : Node.check D_R11111 T2365 [((1605/512),(535/128)),((0),(333/512)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2365_ok
def T2364 : Node := Node.split 1 T2365 T2366
theorem T2364_ok : Node.check D_R11111 T2364 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2365_ok T2366_ok
def T2363 : Node := Node.leaf L2363
theorem T2363_ok : Node.check D_R11111 T2363 [((3745/1024),(535/128)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2363_ok
def T2362 : Node := Node.leaf L2362
theorem T2362_ok : Node.check D_R11111 T2362 [((3745/1024),(535/128)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2362_ok
def T2361 : Node := Node.split 3 T2362 T2363
theorem T2361_ok : Node.check D_R11111 T2361 [((3745/1024),(535/128)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2362_ok T2363_ok
def T2360 : Node := Node.leaf L2360
theorem T2360_ok : Node.check D_R11111 T2360 [((1605/512),(3745/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2360_ok
def T2359 : Node := Node.leaf L2359
theorem T2359_ok : Node.check D_R11111 T2359 [((1605/512),(3745/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2359_ok
def T2358 : Node := Node.split 3 T2359 T2360
theorem T2358_ok : Node.check D_R11111 T2358 [((1605/512),(3745/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2359_ok T2360_ok
def T2357 : Node := Node.split 0 T2358 T2361
theorem T2357_ok : Node.check D_R11111 T2357 [((1605/512),(535/128)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2358_ok T2361_ok
def T2356 : Node := Node.leaf L2356
theorem T2356_ok : Node.check D_R11111 T2356 [((3745/1024),(535/128)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2356_ok
def T2355 : Node := Node.leaf L2355
theorem T2355_ok : Node.check D_R11111 T2355 [((3745/1024),(535/128)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2355_ok
def T2354 : Node := Node.split 3 T2355 T2356
theorem T2354_ok : Node.check D_R11111 T2354 [((3745/1024),(535/128)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2355_ok T2356_ok
def T2353 : Node := Node.leaf L2353
theorem T2353_ok : Node.check D_R11111 T2353 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2353_ok
def T2352 : Node := Node.leaf L2352
theorem T2352_ok : Node.check D_R11111 T2352 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2352_ok
def T2351 : Node := Node.split 3 T2352 T2353
theorem T2351_ok : Node.check D_R11111 T2351 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2352_ok T2353_ok
def T2350 : Node := Node.split 0 T2351 T2354
theorem T2350_ok : Node.check D_R11111 T2350 [((1605/512),(535/128)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2351_ok T2354_ok
def T2349 : Node := Node.split 2 T2350 T2357
theorem T2349_ok : Node.check D_R11111 T2349 [((1605/512),(535/128)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2350_ok T2357_ok
def T2348 : Node := Node.leaf L2348
theorem T2348_ok : Node.check D_R11111 T2348 [((1605/512),(535/128)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2348_ok
def T2347 : Node := Node.split 1 T2348 T2349
theorem T2347_ok : Node.check D_R11111 T2347 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2348_ok T2349_ok
def T2346 : Node := Node.split 3 T2347 T2364
theorem T2346_ok : Node.check D_R11111 T2346 [((1605/512),(535/128)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2347_ok T2364_ok
def T2345 : Node := Node.leaf L2345
theorem T2345_ok : Node.check D_R11111 T2345 [((2675/1024),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2345_ok
def T2344 : Node := Node.leaf L2344
theorem T2344_ok : Node.check D_R11111 T2344 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2344_ok
def T2343 : Node := Node.leaf L2343
theorem T2343_ok : Node.check D_R11111 T2343 [((535/256),(2675/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2343_ok
def T2342 : Node := Node.leaf L2342
theorem T2342_ok : Node.check D_R11111 T2342 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2342_ok
def T2341 : Node := Node.leaf L2341
theorem T2341_ok : Node.check D_R11111 T2341 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2341_ok
def T2340 : Node := Node.leaf L2340
theorem T2340_ok : Node.check D_R11111 T2340 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2340_ok
def T2339 : Node := Node.leaf L2339
theorem T2339_ok : Node.check D_R11111 T2339 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2339_ok
def T2338 : Node := Node.leaf L2338
theorem T2338_ok : Node.check D_R11111 T2338 [((9095/4096),(4815/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2338_ok
def T2337 : Node := Node.leaf L2337
theorem T2337_ok : Node.check D_R11111 T2337 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2337_ok
def T2336 : Node := Node.leaf L2336
theorem T2336_ok : Node.check D_R11111 T2336 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2336_ok
def T2335 : Node := Node.leaf L2335
theorem T2335_ok : Node.check D_R11111 T2335 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2335_ok
def T2334 : Node := Node.split 1 T2335 T2336
theorem T2334_ok : Node.check D_R11111 T2334 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2335_ok T2336_ok
def T2333 : Node := Node.split 3 T2334 T2337
theorem T2333_ok : Node.check D_R11111 T2333 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2334_ok T2337_ok
def T2332 : Node := Node.split 0 T2333 T2338
theorem T2332_ok : Node.check D_R11111 T2332 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2333_ok T2338_ok
def T2331 : Node := Node.split 2 T2332 T2339
theorem T2331_ok : Node.check D_R11111 T2331 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2332_ok T2339_ok
def T2330 : Node := Node.split 1 T2331 T2340
theorem T2330_ok : Node.check D_R11111 T2330 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2331_ok T2340_ok
def T2329 : Node := Node.split 3 T2330 T2341
theorem T2329_ok : Node.check D_R11111 T2329 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2330_ok T2341_ok
def T2328 : Node := Node.split 0 T2329 T2342
theorem T2328_ok : Node.check D_R11111 T2328 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2329_ok T2342_ok
def T2327 : Node := Node.split 2 T2328 T2343
theorem T2327_ok : Node.check D_R11111 T2327 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2328_ok T2343_ok
def T2326 : Node := Node.leaf L2326
theorem T2326_ok : Node.check D_R11111 T2326 [((535/256),(2675/1024)),((333/512),(999/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2326_ok
def T2325 : Node := Node.split 1 T2326 T2327
theorem T2325_ok : Node.check D_R11111 T2325 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2326_ok T2327_ok
def T2324 : Node := Node.split 3 T2325 T2344
theorem T2324_ok : Node.check D_R11111 T2324 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2325_ok T2344_ok
def T2323 : Node := Node.split 0 T2324 T2345
theorem T2323_ok : Node.check D_R11111 T2323 [((535/256),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2324_ok T2345_ok
def T2322 : Node := Node.leaf L2322
theorem T2322_ok : Node.check D_R11111 T2322 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2322_ok
def T2321 : Node := Node.leaf L2321
theorem T2321_ok : Node.check D_R11111 T2321 [((2675/1024),(1605/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2321_ok
def T2320 : Node := Node.leaf L2320
theorem T2320_ok : Node.check D_R11111 T2320 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2320_ok
def T2319 : Node := Node.split 2 T2320 T2321
theorem T2319_ok : Node.check D_R11111 T2319 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2320_ok T2321_ok
def T2318 : Node := Node.leaf L2318
theorem T2318_ok : Node.check D_R11111 T2318 [((2675/1024),(1605/512)),((333/512),(999/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2318_ok
def T2317 : Node := Node.split 1 T2318 T2319
theorem T2317_ok : Node.check D_R11111 T2317 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2318_ok T2319_ok
def T2316 : Node := Node.split 3 T2317 T2322
theorem T2316_ok : Node.check D_R11111 T2316 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2317_ok T2322_ok
def T2315 : Node := Node.leaf L2315
theorem T2315_ok : Node.check D_R11111 T2315 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2315_ok
def T2314 : Node := Node.leaf L2314
theorem T2314_ok : Node.check D_R11111 T2314 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2314_ok
def T2313 : Node := Node.split 1 T2314 T2315
theorem T2313_ok : Node.check D_R11111 T2313 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2314_ok T2315_ok
def T2312 : Node := Node.leaf L2312
theorem T2312_ok : Node.check D_R11111 T2312 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2312_ok
def T2311 : Node := Node.leaf L2311
theorem T2311_ok : Node.check D_R11111 T2311 [((535/256),(4815/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2311_ok
def T2310 : Node := Node.leaf L2310
theorem T2310_ok : Node.check D_R11111 T2310 [((535/256),(4815/2048)),((2331/2048),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2310_ok
def T2309 : Node := Node.leaf L2309
theorem T2309_ok : Node.check D_R11111 T2309 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2309_ok
def T2308 : Node := Node.split 1 T2309 T2310
theorem T2308_ok : Node.check D_R11111 T2308 [((535/256),(4815/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2309_ok T2310_ok
def T2307 : Node := Node.split 3 T2308 T2311
theorem T2307_ok : Node.check D_R11111 T2307 [((535/256),(4815/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2308_ok T2311_ok
def T2306 : Node := Node.split 0 T2307 T2312
theorem T2306_ok : Node.check D_R11111 T2306 [((535/256),(2675/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2307_ok T2312_ok
def T2305 : Node := Node.leaf L2305
theorem T2305_ok : Node.check D_R11111 T2305 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2305_ok
def T2304 : Node := Node.split 2 T2305 T2306
theorem T2304_ok : Node.check D_R11111 T2304 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2305_ok T2306_ok
def T2303 : Node := Node.leaf L2303
theorem T2303_ok : Node.check D_R11111 T2303 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2303_ok
def T2302 : Node := Node.split 1 T2303 T2304
theorem T2302_ok : Node.check D_R11111 T2302 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2303_ok T2304_ok
def T2301 : Node := Node.split 3 T2302 T2313
theorem T2301_ok : Node.check D_R11111 T2301 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2302_ok T2313_ok
def T2300 : Node := Node.split 0 T2301 T2316
theorem T2300_ok : Node.check D_R11111 T2300 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2301_ok T2316_ok
def T2299 : Node := Node.split 2 T2300 T2323
theorem T2299_ok : Node.check D_R11111 T2299 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2300_ok T2323_ok
def T2298 : Node := Node.leaf L2298
theorem T2298_ok : Node.check D_R11111 T2298 [((535/256),(1605/512)),((0),(333/512)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2298_ok
def T2297 : Node := Node.split 1 T2298 T2299
theorem T2297_ok : Node.check D_R11111 T2297 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2298_ok T2299_ok
def T2296 : Node := Node.leaf L2296
theorem T2296_ok : Node.check D_R11111 T2296 [((2675/1024),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2296_ok
def T2295 : Node := Node.leaf L2295
theorem T2295_ok : Node.check D_R11111 T2295 [((2675/1024),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2295_ok
def T2294 : Node := Node.split 3 T2295 T2296
theorem T2294_ok : Node.check D_R11111 T2294 [((2675/1024),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2295_ok T2296_ok
def T2293 : Node := Node.leaf L2293
theorem T2293_ok : Node.check D_R11111 T2293 [((535/256),(2675/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2293_ok
def T2292 : Node := Node.leaf L2292
theorem T2292_ok : Node.check D_R11111 T2292 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2292_ok
def T2291 : Node := Node.leaf L2291
theorem T2291_ok : Node.check D_R11111 T2291 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2291_ok
def T2290 : Node := Node.leaf L2290
theorem T2290_ok : Node.check D_R11111 T2290 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2290_ok
def T2289 : Node := Node.leaf L2289
theorem T2289_ok : Node.check D_R11111 T2289 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2289_ok
def T2288 : Node := Node.split 2 T2289 T2290
theorem T2288_ok : Node.check D_R11111 T2288 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2289_ok T2290_ok
def T2287 : Node := Node.split 1 T2288 T2291
theorem T2287_ok : Node.check D_R11111 T2287 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2288_ok T2291_ok
def T2286 : Node := Node.leaf L2286
theorem T2286_ok : Node.check D_R11111 T2286 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2286_ok
def T2285 : Node := Node.split 3 T2286 T2287
theorem T2285_ok : Node.check D_R11111 T2285 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2286_ok T2287_ok
def T2284 : Node := Node.split 0 T2285 T2292
theorem T2284_ok : Node.check D_R11111 T2284 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2285_ok T2292_ok
def T2283 : Node := Node.split 2 T2284 T2293
theorem T2283_ok : Node.check D_R11111 T2283 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2284_ok T2293_ok
def T2282 : Node := Node.leaf L2282
theorem T2282_ok : Node.check D_R11111 T2282 [((535/256),(2675/1024)),((333/512),(999/1024)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2282_ok
def T2281 : Node := Node.split 1 T2282 T2283
theorem T2281_ok : Node.check D_R11111 T2281 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2282_ok T2283_ok
def T2280 : Node := Node.leaf L2280
theorem T2280_ok : Node.check D_R11111 T2280 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2280_ok
def T2279 : Node := Node.split 3 T2280 T2281
theorem T2279_ok : Node.check D_R11111 T2279 [((535/256),(2675/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2280_ok T2281_ok
def T2278 : Node := Node.split 0 T2279 T2294
theorem T2278_ok : Node.check D_R11111 T2278 [((535/256),(1605/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2279_ok T2294_ok
def T2277 : Node := Node.leaf L2277
theorem T2277_ok : Node.check D_R11111 T2277 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2277_ok
def T2276 : Node := Node.leaf L2276
theorem T2276_ok : Node.check D_R11111 T2276 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2276_ok
def T2275 : Node := Node.split 3 T2276 T2277
theorem T2275_ok : Node.check D_R11111 T2275 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2276_ok T2277_ok
def T2274 : Node := Node.leaf L2274
theorem T2274_ok : Node.check D_R11111 T2274 [((535/256),(2675/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2274_ok
def T2273 : Node := Node.leaf L2273
theorem T2273_ok : Node.check D_R11111 T2273 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2273_ok
def T2272 : Node := Node.split 2 T2273 T2274
theorem T2272_ok : Node.check D_R11111 T2272 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2273_ok T2274_ok
def T2271 : Node := Node.leaf L2271
theorem T2271_ok : Node.check D_R11111 T2271 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2271_ok
def T2270 : Node := Node.split 1 T2271 T2272
theorem T2270_ok : Node.check D_R11111 T2270 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2271_ok T2272_ok
def T2269 : Node := Node.leaf L2269
theorem T2269_ok : Node.check D_R11111 T2269 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2269_ok
def T2268 : Node := Node.split 3 T2269 T2270
theorem T2268_ok : Node.check D_R11111 T2268 [((535/256),(2675/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2269_ok T2270_ok
def T2267 : Node := Node.split 0 T2268 T2275
theorem T2267_ok : Node.check D_R11111 T2267 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2268_ok T2275_ok
def T2266 : Node := Node.split 2 T2267 T2278
theorem T2266_ok : Node.check D_R11111 T2266 [((535/256),(1605/512)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2267_ok T2278_ok
def T2265 : Node := Node.leaf L2265
theorem T2265_ok : Node.check D_R11111 T2265 [((535/256),(1605/512)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2265_ok
def T2264 : Node := Node.split 1 T2265 T2266
theorem T2264_ok : Node.check D_R11111 T2264 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2265_ok T2266_ok
def T2263 : Node := Node.split 3 T2264 T2297
theorem T2263_ok : Node.check D_R11111 T2263 [((535/256),(1605/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2264_ok T2297_ok
def T2262 : Node := Node.split 0 T2263 T2346
theorem T2262_ok : Node.check D_R11111 T2262 [((535/256),(535/128)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2263_ok T2346_ok
def T2261 : Node := Node.leaf L2261
theorem T2261_ok : Node.check D_R11111 T2261 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2261_ok
def T2260 : Node := Node.leaf L2260
theorem T2260_ok : Node.check D_R11111 T2260 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2260_ok
def T2259 : Node := Node.leaf L2259
theorem T2259_ok : Node.check D_R11111 T2259 [((8025/2048),(535/128)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2259_ok
def T2258 : Node := Node.leaf L2258
theorem T2258_ok : Node.check D_R11111 T2258 [((8025/2048),(535/128)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2258_ok
def T2257 : Node := Node.leaf L2257
theorem T2257_ok : Node.check D_R11111 T2257 [((8025/2048),(535/128)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2257_ok
def T2256 : Node := Node.split 2 T2257 T2258
theorem T2256_ok : Node.check D_R11111 T2256 [((8025/2048),(535/128)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2257_ok T2258_ok
def T2255 : Node := Node.split 1 T2256 T2259
theorem T2255_ok : Node.check D_R11111 T2255 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2256_ok T2259_ok
def T2254 : Node := Node.split 3 T2255 T2260
theorem T2254_ok : Node.check D_R11111 T2254 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2255_ok T2260_ok
def T2253 : Node := Node.leaf L2253
theorem T2253_ok : Node.check D_R11111 T2253 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2253_ok
def T2252 : Node := Node.leaf L2252
theorem T2252_ok : Node.check D_R11111 T2252 [((3745/1024),(8025/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2252_ok
def T2251 : Node := Node.leaf L2251
theorem T2251_ok : Node.check D_R11111 T2251 [((3745/1024),(8025/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2251_ok
def T2250 : Node := Node.leaf L2250
theorem T2250_ok : Node.check D_R11111 T2250 [((3745/1024),(8025/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2250_ok
def T2249 : Node := Node.split 2 T2250 T2251
theorem T2249_ok : Node.check D_R11111 T2249 [((3745/1024),(8025/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2250_ok T2251_ok
def T2248 : Node := Node.split 1 T2249 T2252
theorem T2248_ok : Node.check D_R11111 T2248 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2249_ok T2252_ok
def T2247 : Node := Node.split 3 T2248 T2253
theorem T2247_ok : Node.check D_R11111 T2247 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2248_ok T2253_ok
def T2246 : Node := Node.split 0 T2247 T2254
theorem T2246_ok : Node.check D_R11111 T2246 [((3745/1024),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2247_ok T2254_ok
def T2245 : Node := Node.leaf L2245
theorem T2245_ok : Node.check D_R11111 T2245 [((3745/1024),(535/128)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2245_ok
def T2244 : Node := Node.split 2 T2245 T2246
theorem T2244_ok : Node.check D_R11111 T2244 [((3745/1024),(535/128)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2245_ok T2246_ok
def T2243 : Node := Node.leaf L2243
theorem T2243_ok : Node.check D_R11111 T2243 [((3745/1024),(535/128)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2243_ok
def T2242 : Node := Node.split 1 T2243 T2244
theorem T2242_ok : Node.check D_R11111 T2242 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2243_ok T2244_ok
def T2241 : Node := Node.split 3 T2242 T2261
theorem T2241_ok : Node.check D_R11111 T2241 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2242_ok T2261_ok
def T2240 : Node := Node.leaf L2240
theorem T2240_ok : Node.check D_R11111 T2240 [((6955/2048),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2240_ok
def T2239 : Node := Node.leaf L2239
theorem T2239_ok : Node.check D_R11111 T2239 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2239_ok
def T2238 : Node := Node.split 0 T2239 T2240
theorem T2238_ok : Node.check D_R11111 T2238 [((1605/512),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2239_ok T2240_ok
def T2237 : Node := Node.leaf L2237
theorem T2237_ok : Node.check D_R11111 T2237 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2237_ok
def T2236 : Node := Node.split 2 T2237 T2238
theorem T2236_ok : Node.check D_R11111 T2236 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2237_ok T2238_ok
def T2235 : Node := Node.leaf L2235
theorem T2235_ok : Node.check D_R11111 T2235 [((1605/512),(3745/1024)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2235_ok
def T2234 : Node := Node.split 1 T2235 T2236
theorem T2234_ok : Node.check D_R11111 T2234 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2235_ok T2236_ok
def T2233 : Node := Node.leaf L2233
theorem T2233_ok : Node.check D_R11111 T2233 [((6955/2048),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2233_ok
def T2232 : Node := Node.leaf L2232
theorem T2232_ok : Node.check D_R11111 T2232 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2232_ok
def T2231 : Node := Node.leaf L2231
theorem T2231_ok : Node.check D_R11111 T2231 [((1605/512),(6955/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2231_ok
def T2230 : Node := Node.leaf L2230
theorem T2230_ok : Node.check D_R11111 T2230 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2230_ok
def T2229 : Node := Node.leaf L2229
theorem T2229_ok : Node.check D_R11111 T2229 [((13375/4096),(6955/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2229_ok
def T2228 : Node := Node.leaf L2228
theorem T2228_ok : Node.check D_R11111 T2228 [((1605/512),(13375/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2228_ok
def T2227 : Node := Node.split 0 T2228 T2229
theorem T2227_ok : Node.check D_R11111 T2227 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2228_ok T2229_ok
def T2226 : Node := Node.split 2 T2227 T2230
theorem T2226_ok : Node.check D_R11111 T2226 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2227_ok T2230_ok
def T2225 : Node := Node.split 1 T2226 T2231
theorem T2225_ok : Node.check D_R11111 T2225 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2226_ok T2231_ok
def T2224 : Node := Node.split 3 T2225 T2232
theorem T2224_ok : Node.check D_R11111 T2224 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2225_ok T2232_ok
def T2223 : Node := Node.split 0 T2224 T2233
theorem T2223_ok : Node.check D_R11111 T2223 [((1605/512),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2224_ok T2233_ok
def T2222 : Node := Node.leaf L2222
theorem T2222_ok : Node.check D_R11111 T2222 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2222_ok
def T2221 : Node := Node.split 2 T2222 T2223
theorem T2221_ok : Node.check D_R11111 T2221 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2222_ok T2223_ok
def T2220 : Node := Node.leaf L2220
theorem T2220_ok : Node.check D_R11111 T2220 [((1605/512),(3745/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2220_ok
def T2219 : Node := Node.split 1 T2220 T2221
theorem T2219_ok : Node.check D_R11111 T2219 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2220_ok T2221_ok
def T2218 : Node := Node.split 3 T2219 T2234
theorem T2218_ok : Node.check D_R11111 T2218 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2219_ok T2234_ok
def T2217 : Node := Node.split 0 T2218 T2241
theorem T2217_ok : Node.check D_R11111 T2217 [((1605/512),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2218_ok T2241_ok
def T2216 : Node := Node.leaf L2216
theorem T2216_ok : Node.check D_R11111 T2216 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2216_ok
def T2215 : Node := Node.split 2 T2216 T2217
theorem T2215_ok : Node.check D_R11111 T2215 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2216_ok T2217_ok
def T2214 : Node := Node.leaf L2214
theorem T2214_ok : Node.check D_R11111 T2214 [((1605/512),(535/128)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2214_ok
def T2213 : Node := Node.split 1 T2214 T2215
theorem T2213_ok : Node.check D_R11111 T2213 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2214_ok T2215_ok
def T2212 : Node := Node.leaf L2212
theorem T2212_ok : Node.check D_R11111 T2212 [((8025/2048),(535/128)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2212_ok
def T2211 : Node := Node.leaf L2211
theorem T2211_ok : Node.check D_R11111 T2211 [((8025/2048),(535/128)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2211_ok
def T2210 : Node := Node.split 1 T2211 T2212
theorem T2210_ok : Node.check D_R11111 T2210 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2211_ok T2212_ok
def T2209 : Node := Node.leaf L2209
theorem T2209_ok : Node.check D_R11111 T2209 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2209_ok
def T2208 : Node := Node.split 3 T2209 T2210
theorem T2208_ok : Node.check D_R11111 T2208 [((8025/2048),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2209_ok T2210_ok
def T2207 : Node := Node.leaf L2207
theorem T2207_ok : Node.check D_R11111 T2207 [((3745/1024),(8025/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2207_ok
def T2206 : Node := Node.leaf L2206
theorem T2206_ok : Node.check D_R11111 T2206 [((3745/1024),(8025/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2206_ok
def T2205 : Node := Node.split 1 T2206 T2207
theorem T2205_ok : Node.check D_R11111 T2205 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2206_ok T2207_ok
def T2204 : Node := Node.leaf L2204
theorem T2204_ok : Node.check D_R11111 T2204 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2204_ok
def T2203 : Node := Node.split 3 T2204 T2205
theorem T2203_ok : Node.check D_R11111 T2203 [((3745/1024),(8025/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2204_ok T2205_ok
def T2202 : Node := Node.split 0 T2203 T2208
theorem T2202_ok : Node.check D_R11111 T2202 [((3745/1024),(535/128)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2203_ok T2208_ok
def T2201 : Node := Node.leaf L2201
theorem T2201_ok : Node.check D_R11111 T2201 [((3745/1024),(535/128)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2201_ok
def T2200 : Node := Node.split 2 T2201 T2202
theorem T2200_ok : Node.check D_R11111 T2200 [((3745/1024),(535/128)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2201_ok T2202_ok
def T2199 : Node := Node.leaf L2199
theorem T2199_ok : Node.check D_R11111 T2199 [((3745/1024),(535/128)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2199_ok
def T2198 : Node := Node.split 1 T2199 T2200
theorem T2198_ok : Node.check D_R11111 T2198 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2199_ok T2200_ok
def T2197 : Node := Node.leaf L2197
theorem T2197_ok : Node.check D_R11111 T2197 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2197_ok
def T2196 : Node := Node.split 3 T2197 T2198
theorem T2196_ok : Node.check D_R11111 T2196 [((3745/1024),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2197_ok T2198_ok
def T2195 : Node := Node.leaf L2195
theorem T2195_ok : Node.check D_R11111 T2195 [((6955/2048),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2195_ok
def T2194 : Node := Node.leaf L2194
theorem T2194_ok : Node.check D_R11111 T2194 [((1605/512),(6955/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2194_ok
def T2193 : Node := Node.leaf L2193
theorem T2193_ok : Node.check D_R11111 T2193 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2193_ok
def T2192 : Node := Node.leaf L2192
theorem T2192_ok : Node.check D_R11111 T2192 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2192_ok
def T2191 : Node := Node.split 2 T2192 T2193
theorem T2191_ok : Node.check D_R11111 T2191 [((1605/512),(6955/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2192_ok T2193_ok
def T2190 : Node := Node.split 1 T2191 T2194
theorem T2190_ok : Node.check D_R11111 T2190 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2191_ok T2194_ok
def T2189 : Node := Node.leaf L2189
theorem T2189_ok : Node.check D_R11111 T2189 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2189_ok
def T2188 : Node := Node.split 3 T2189 T2190
theorem T2188_ok : Node.check D_R11111 T2188 [((1605/512),(6955/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2189_ok T2190_ok
def T2187 : Node := Node.split 0 T2188 T2195
theorem T2187_ok : Node.check D_R11111 T2187 [((1605/512),(3745/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2188_ok T2195_ok
def T2186 : Node := Node.leaf L2186
theorem T2186_ok : Node.check D_R11111 T2186 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2186_ok
def T2185 : Node := Node.split 2 T2186 T2187
theorem T2185_ok : Node.check D_R11111 T2185 [((1605/512),(3745/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2186_ok T2187_ok
def T2184 : Node := Node.leaf L2184
theorem T2184_ok : Node.check D_R11111 T2184 [((1605/512),(3745/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2184_ok
def T2183 : Node := Node.split 1 T2184 T2185
theorem T2183_ok : Node.check D_R11111 T2183 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2184_ok T2185_ok
def T2182 : Node := Node.leaf L2182
theorem T2182_ok : Node.check D_R11111 T2182 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2182_ok
def T2181 : Node := Node.split 3 T2182 T2183
theorem T2181_ok : Node.check D_R11111 T2181 [((1605/512),(3745/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2182_ok T2183_ok
def T2180 : Node := Node.split 0 T2181 T2196
theorem T2180_ok : Node.check D_R11111 T2180 [((1605/512),(535/128)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2181_ok T2196_ok
def T2179 : Node := Node.leaf L2179
theorem T2179_ok : Node.check D_R11111 T2179 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2179_ok
def T2178 : Node := Node.split 2 T2179 T2180
theorem T2178_ok : Node.check D_R11111 T2178 [((1605/512),(535/128)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2179_ok T2180_ok
def T2177 : Node := Node.leaf L2177
theorem T2177_ok : Node.check D_R11111 T2177 [((1605/512),(535/128)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L2177_ok
def T2176 : Node := Node.split 1 T2177 T2178
theorem T2176_ok : Node.check D_R11111 T2176 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2177_ok T2178_ok
def T2175 : Node := Node.split 3 T2176 T2213
theorem T2175_ok : Node.check D_R11111 T2175 [((1605/512),(535/128)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2176_ok T2213_ok
def T2174 : Node := Node.leaf L2174
theorem T2174_ok : Node.check D_R11111 T2174 [((5885/2048),(1605/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2174_ok
def T2173 : Node := Node.leaf L2173
theorem T2173_ok : Node.check D_R11111 T2173 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2173_ok
def T2172 : Node := Node.leaf L2172
theorem T2172_ok : Node.check D_R11111 T2172 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2172_ok
def T2171 : Node := Node.split 2 T2172 T2173
theorem T2171_ok : Node.check D_R11111 T2171 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2172_ok T2173_ok
def T2170 : Node := Node.split 1 T2171 T2174
theorem T2170_ok : Node.check D_R11111 T2170 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2171_ok T2174_ok
def T2169 : Node := Node.leaf L2169
theorem T2169_ok : Node.check D_R11111 T2169 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L2169_ok
def T2168 : Node := Node.split 3 T2169 T2170
theorem T2168_ok : Node.check D_R11111 T2168 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2169_ok T2170_ok
def T2167 : Node := Node.leaf L2167
theorem T2167_ok : Node.check D_R11111 T2167 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2167_ok
def T2166 : Node := Node.leaf L2166
theorem T2166_ok : Node.check D_R11111 T2166 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L2166_ok
def T2165 : Node := Node.split 3 T2166 T2167
theorem T2165_ok : Node.check D_R11111 T2165 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2166_ok T2167_ok
def T2164 : Node := Node.split 0 T2165 T2168
theorem T2164_ok : Node.check D_R11111 T2164 [((2675/1024),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2165_ok T2168_ok
def T2163 : Node := Node.leaf L2163
theorem T2163_ok : Node.check D_R11111 T2163 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2163_ok
def T2162 : Node := Node.split 2 T2163 T2164
theorem T2162_ok : Node.check D_R11111 T2162 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2163_ok T2164_ok
def T2161 : Node := Node.leaf L2161
theorem T2161_ok : Node.check D_R11111 T2161 [((2675/1024),(1605/512)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2161_ok
def T2160 : Node := Node.split 1 T2161 T2162
theorem T2160_ok : Node.check D_R11111 T2160 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2161_ok T2162_ok
def T2159 : Node := Node.leaf L2159
theorem T2159_ok : Node.check D_R11111 T2159 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2159_ok
def T2158 : Node := Node.leaf L2158
theorem T2158_ok : Node.check D_R11111 T2158 [((5885/2048),(1605/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2158_ok
def T2157 : Node := Node.leaf L2157
theorem T2157_ok : Node.check D_R11111 T2157 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2157_ok
def T2156 : Node := Node.leaf L2156
theorem T2156_ok : Node.check D_R11111 T2156 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2156_ok
def T2155 : Node := Node.leaf L2155
theorem T2155_ok : Node.check D_R11111 T2155 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2155_ok
def T2154 : Node := Node.leaf L2154
theorem T2154_ok : Node.check D_R11111 T2154 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2154_ok
def T2153 : Node := Node.split 2 T2154 T2155
theorem T2153_ok : Node.check D_R11111 T2153 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2154_ok T2155_ok
def T2152 : Node := Node.leaf L2152
theorem T2152_ok : Node.check D_R11111 T2152 [((12305/4096),(1605/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2152_ok
def T2151 : Node := Node.leaf L2151
theorem T2151_ok : Node.check D_R11111 T2151 [((12305/4096),(1605/512)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2151_ok
def T2150 : Node := Node.split 2 T2151 T2152
theorem T2150_ok : Node.check D_R11111 T2150 [((12305/4096),(1605/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2151_ok T2152_ok
def T2149 : Node := Node.split 1 T2150 T2153
theorem T2149_ok : Node.check D_R11111 T2149 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2150_ok T2153_ok
def T2148 : Node := Node.split 3 T2149 T2156
theorem T2148_ok : Node.check D_R11111 T2148 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2149_ok T2156_ok
def T2147 : Node := Node.leaf L2147
theorem T2147_ok : Node.check D_R11111 T2147 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2147_ok
def T2146 : Node := Node.leaf L2146
theorem T2146_ok : Node.check D_R11111 T2146 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2146_ok
def T2145 : Node := Node.leaf L2145
theorem T2145_ok : Node.check D_R11111 T2145 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2145_ok
def T2144 : Node := Node.split 2 T2145 T2146
theorem T2144_ok : Node.check D_R11111 T2144 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2145_ok T2146_ok
def T2143 : Node := Node.leaf L2143
theorem T2143_ok : Node.check D_R11111 T2143 [((5885/2048),(12305/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2143_ok
def T2142 : Node := Node.leaf L2142
theorem T2142_ok : Node.check D_R11111 T2142 [((5885/2048),(12305/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2142_ok
def T2141 : Node := Node.split 2 T2142 T2143
theorem T2141_ok : Node.check D_R11111 T2141 [((5885/2048),(12305/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2142_ok T2143_ok
def T2140 : Node := Node.split 1 T2141 T2144
theorem T2140_ok : Node.check D_R11111 T2140 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2141_ok T2144_ok
def T2139 : Node := Node.split 3 T2140 T2147
theorem T2139_ok : Node.check D_R11111 T2139 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2140_ok T2147_ok
def T2138 : Node := Node.split 0 T2139 T2148
theorem T2138_ok : Node.check D_R11111 T2138 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2139_ok T2148_ok
def T2137 : Node := Node.split 2 T2138 T2157
theorem T2137_ok : Node.check D_R11111 T2137 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2138_ok T2157_ok
def T2136 : Node := Node.split 1 T2137 T2158
theorem T2136_ok : Node.check D_R11111 T2136 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2137_ok T2158_ok
def T2135 : Node := Node.split 3 T2136 T2159
theorem T2135_ok : Node.check D_R11111 T2135 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2136_ok T2159_ok
def T2134 : Node := Node.leaf L2134
theorem T2134_ok : Node.check D_R11111 T2134 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2134_ok
def T2133 : Node := Node.leaf L2133
theorem T2133_ok : Node.check D_R11111 T2133 [((2675/1024),(5885/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2133_ok
def T2132 : Node := Node.leaf L2132
theorem T2132_ok : Node.check D_R11111 T2132 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2132_ok
def T2131 : Node := Node.leaf L2131
theorem T2131_ok : Node.check D_R11111 T2131 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2131_ok
def T2130 : Node := Node.leaf L2130
theorem T2130_ok : Node.check D_R11111 T2130 [((11235/4096),(5885/2048)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2130_ok
def T2129 : Node := Node.leaf L2129
theorem T2129_ok : Node.check D_R11111 T2129 [((11235/4096),(5885/2048)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2129_ok
def T2128 : Node := Node.split 2 T2129 T2130
theorem T2128_ok : Node.check D_R11111 T2128 [((11235/4096),(5885/2048)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2129_ok T2130_ok
def T2127 : Node := Node.leaf L2127
theorem T2127_ok : Node.check D_R11111 T2127 [((11235/4096),(5885/2048)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2127_ok
def T2126 : Node := Node.split 1 T2127 T2128
theorem T2126_ok : Node.check D_R11111 T2126 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2127_ok T2128_ok
def T2125 : Node := Node.split 3 T2126 T2131
theorem T2125_ok : Node.check D_R11111 T2125 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2126_ok T2131_ok
def T2124 : Node := Node.leaf L2124
theorem T2124_ok : Node.check D_R11111 T2124 [((2675/1024),(11235/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2124_ok
def T2123 : Node := Node.split 0 T2124 T2125
theorem T2123_ok : Node.check D_R11111 T2123 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2124_ok T2125_ok
def T2122 : Node := Node.split 2 T2123 T2132
theorem T2122_ok : Node.check D_R11111 T2122 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2123_ok T2132_ok
def T2121 : Node := Node.split 1 T2122 T2133
theorem T2121_ok : Node.check D_R11111 T2121 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2122_ok T2133_ok
def T2120 : Node := Node.split 3 T2121 T2134
theorem T2120_ok : Node.check D_R11111 T2120 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2121_ok T2134_ok
def T2119 : Node := Node.split 0 T2120 T2135
theorem T2119_ok : Node.check D_R11111 T2119 [((2675/1024),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2120_ok T2135_ok
def T2118 : Node := Node.leaf L2118
theorem T2118_ok : Node.check D_R11111 T2118 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2118_ok
def T2117 : Node := Node.split 2 T2118 T2119
theorem T2117_ok : Node.check D_R11111 T2117 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2118_ok T2119_ok
def T2116 : Node := Node.leaf L2116
theorem T2116_ok : Node.check D_R11111 T2116 [((2675/1024),(1605/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2116_ok
def T2115 : Node := Node.split 1 T2116 T2117
theorem T2115_ok : Node.check D_R11111 T2115 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2116_ok T2117_ok
def T2114 : Node := Node.split 3 T2115 T2160
theorem T2114_ok : Node.check D_R11111 T2114 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2115_ok T2160_ok
def T2113 : Node := Node.leaf L2113
theorem T2113_ok : Node.check D_R11111 T2113 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2113_ok
def T2112 : Node := Node.leaf L2112
theorem T2112_ok : Node.check D_R11111 T2112 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2112_ok
def T2111 : Node := Node.leaf L2111
theorem T2111_ok : Node.check D_R11111 T2111 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2111_ok
def T2110 : Node := Node.leaf L2110
theorem T2110_ok : Node.check D_R11111 T2110 [((9095/4096),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L2110_ok
def T2109 : Node := Node.leaf L2109
theorem T2109_ok : Node.check D_R11111 T2109 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L2109_ok
def T2108 : Node := Node.leaf L2108
theorem T2108_ok : Node.check D_R11111 T2108 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L2108_ok
def T2107 : Node := Node.split 1 T2108 T2109
theorem T2107_ok : Node.check D_R11111 T2107 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2108_ok T2109_ok
def T2106 : Node := Node.leaf L2106
theorem T2106_ok : Node.check D_R11111 T2106 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L2106_ok
def T2105 : Node := Node.leaf L2105
theorem T2105_ok : Node.check D_R11111 T2105 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L2105_ok
def T2104 : Node := Node.split 1 T2105 T2106
theorem T2104_ok : Node.check D_R11111 T2104 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2105_ok T2106_ok
def T2103 : Node := Node.split 3 T2104 T2107
theorem T2103_ok : Node.check D_R11111 T2103 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2104_ok T2107_ok
def T2102 : Node := Node.split 0 T2103 T2110
theorem T2102_ok : Node.check D_R11111 T2102 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2103_ok T2110_ok
def T2101 : Node := Node.split 2 T2102 T2111
theorem T2101_ok : Node.check D_R11111 T2101 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2102_ok T2111_ok
def T2100 : Node := Node.split 1 T2101 T2112
theorem T2100_ok : Node.check D_R11111 T2100 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2101_ok T2112_ok
def T2099 : Node := Node.leaf L2099
theorem T2099_ok : Node.check D_R11111 T2099 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L2099_ok
def T2098 : Node := Node.split 3 T2099 T2100
theorem T2098_ok : Node.check D_R11111 T2098 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2099_ok T2100_ok
def T2097 : Node := Node.split 0 T2098 T2113
theorem T2097_ok : Node.check D_R11111 T2097 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2098_ok T2113_ok
def T2096 : Node := Node.leaf L2096
theorem T2096_ok : Node.check D_R11111 T2096 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2096_ok
def T2095 : Node := Node.split 2 T2096 T2097
theorem T2095_ok : Node.check D_R11111 T2095 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2096_ok T2097_ok
def T2094 : Node := Node.leaf L2094
theorem T2094_ok : Node.check D_R11111 T2094 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L2094_ok
def T2093 : Node := Node.split 1 T2094 T2095
theorem T2093_ok : Node.check D_R11111 T2093 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2094_ok T2095_ok
def T2092 : Node := Node.leaf L2092
theorem T2092_ok : Node.check D_R11111 T2092 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2092_ok
def T2091 : Node := Node.leaf L2091
theorem T2091_ok : Node.check D_R11111 T2091 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2091_ok
def T2090 : Node := Node.leaf L2090
theorem T2090_ok : Node.check D_R11111 T2090 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2090_ok
def T2089 : Node := Node.leaf L2089
theorem T2089_ok : Node.check D_R11111 T2089 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2089_ok
def T2088 : Node := Node.leaf L2088
theorem T2088_ok : Node.check D_R11111 T2088 [((9095/4096),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2088_ok
def T2087 : Node := Node.leaf L2087
theorem T2087_ok : Node.check D_R11111 T2087 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L2087_ok
def T2086 : Node := Node.leaf L2086
theorem T2086_ok : Node.check D_R11111 T2086 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2086_ok
def T2085 : Node := Node.leaf L2085
theorem T2085_ok : Node.check D_R11111 T2085 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2085_ok
def T2084 : Node := Node.split 2 T2085 T2086
theorem T2084_ok : Node.check D_R11111 T2084 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2085_ok T2086_ok
def T2083 : Node := Node.leaf L2083
theorem T2083_ok : Node.check D_R11111 T2083 [((17655/8192),(9095/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2083_ok
def T2082 : Node := Node.leaf L2082
theorem T2082_ok : Node.check D_R11111 T2082 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2082_ok
def T2081 : Node := Node.split 0 T2082 T2083
theorem T2081_ok : Node.check D_R11111 T2081 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2082_ok T2083_ok
def T2080 : Node := Node.leaf L2080
theorem T2080_ok : Node.check D_R11111 T2080 [((17655/8192),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2080_ok
def T2079 : Node := Node.leaf L2079
theorem T2079_ok : Node.check D_R11111 T2079 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L2079_ok
def T2078 : Node := Node.leaf L2078
theorem T2078_ok : Node.check D_R11111 T2078 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L2078_ok
def T2077 : Node := Node.split 3 T2078 T2079
theorem T2077_ok : Node.check D_R11111 T2077 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2078_ok T2079_ok
def T2076 : Node := Node.split 0 T2077 T2080
theorem T2076_ok : Node.check D_R11111 T2076 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2077_ok T2080_ok
def T2075 : Node := Node.split 2 T2076 T2081
theorem T2075_ok : Node.check D_R11111 T2075 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2076_ok T2081_ok
def T2074 : Node := Node.split 1 T2075 T2084
theorem T2074_ok : Node.check D_R11111 T2074 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2075_ok T2084_ok
def T2073 : Node := Node.split 3 T2074 T2087
theorem T2073_ok : Node.check D_R11111 T2073 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2074_ok T2087_ok
def T2072 : Node := Node.split 0 T2073 T2088
theorem T2072_ok : Node.check D_R11111 T2072 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2073_ok T2088_ok
def T2071 : Node := Node.split 2 T2072 T2089
theorem T2071_ok : Node.check D_R11111 T2071 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2072_ok T2089_ok
def T2070 : Node := Node.split 1 T2071 T2090
theorem T2070_ok : Node.check D_R11111 T2070 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2071_ok T2090_ok
def T2069 : Node := Node.split 3 T2070 T2091
theorem T2069_ok : Node.check D_R11111 T2069 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2070_ok T2091_ok
def T2068 : Node := Node.split 0 T2069 T2092
theorem T2068_ok : Node.check D_R11111 T2068 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2069_ok T2092_ok
def T2067 : Node := Node.leaf L2067
theorem T2067_ok : Node.check D_R11111 T2067 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2067_ok
def T2066 : Node := Node.split 2 T2067 T2068
theorem T2066_ok : Node.check D_R11111 T2066 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2067_ok T2068_ok
def T2065 : Node := Node.leaf L2065
theorem T2065_ok : Node.check D_R11111 T2065 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L2065_ok
def T2064 : Node := Node.split 1 T2065 T2066
theorem T2064_ok : Node.check D_R11111 T2064 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2065_ok T2066_ok
def T2063 : Node := Node.split 3 T2064 T2093
theorem T2063_ok : Node.check D_R11111 T2063 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2064_ok T2093_ok
def T2062 : Node := Node.split 0 T2063 T2114
theorem T2062_ok : Node.check D_R11111 T2062 [((535/256),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2063_ok T2114_ok
def T2061 : Node := Node.leaf L2061
theorem T2061_ok : Node.check D_R11111 T2061 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2061_ok
def T2060 : Node := Node.split 2 T2061 T2062
theorem T2060_ok : Node.check D_R11111 T2060 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2061_ok T2062_ok
def T2059 : Node := Node.leaf L2059
theorem T2059_ok : Node.check D_R11111 T2059 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L2059_ok
def T2058 : Node := Node.split 1 T2059 T2060
theorem T2058_ok : Node.check D_R11111 T2058 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2059_ok T2060_ok
def T2057 : Node := Node.leaf L2057
theorem T2057_ok : Node.check D_R11111 T2057 [((5885/2048),(1605/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2057_ok
def T2056 : Node := Node.leaf L2056
theorem T2056_ok : Node.check D_R11111 T2056 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2056_ok
def T2055 : Node := Node.leaf L2055
theorem T2055_ok : Node.check D_R11111 T2055 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2055_ok
def T2054 : Node := Node.leaf L2054
theorem T2054_ok : Node.check D_R11111 T2054 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2054_ok
def T2053 : Node := Node.split 2 T2054 T2055
theorem T2053_ok : Node.check D_R11111 T2053 [((12305/4096),(1605/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2054_ok T2055_ok
def T2052 : Node := Node.leaf L2052
theorem T2052_ok : Node.check D_R11111 T2052 [((12305/4096),(1605/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2052_ok
def T2051 : Node := Node.split 1 T2052 T2053
theorem T2051_ok : Node.check D_R11111 T2051 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2052_ok T2053_ok
def T2050 : Node := Node.leaf L2050
theorem T2050_ok : Node.check D_R11111 T2050 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L2050_ok
def T2049 : Node := Node.split 3 T2050 T2051
theorem T2049_ok : Node.check D_R11111 T2049 [((12305/4096),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2050_ok T2051_ok
def T2048 : Node := Node.leaf L2048
theorem T2048_ok : Node.check D_R11111 T2048 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2048_ok
def T2047 : Node := Node.leaf L2047
theorem T2047_ok : Node.check D_R11111 T2047 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2047_ok
def T2046 : Node := Node.split 2 T2047 T2048
theorem T2046_ok : Node.check D_R11111 T2046 [((5885/2048),(12305/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2047_ok T2048_ok
def T2045 : Node := Node.leaf L2045
theorem T2045_ok : Node.check D_R11111 T2045 [((5885/2048),(12305/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2045_ok
def T2044 : Node := Node.split 1 T2045 T2046
theorem T2044_ok : Node.check D_R11111 T2044 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2045_ok T2046_ok
def T2043 : Node := Node.leaf L2043
theorem T2043_ok : Node.check D_R11111 T2043 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L2043_ok
def T2042 : Node := Node.split 3 T2043 T2044
theorem T2042_ok : Node.check D_R11111 T2042 [((5885/2048),(12305/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2043_ok T2044_ok
def T2041 : Node := Node.split 0 T2042 T2049
theorem T2041_ok : Node.check D_R11111 T2041 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2042_ok T2049_ok
def T2040 : Node := Node.split 2 T2041 T2056
theorem T2040_ok : Node.check D_R11111 T2040 [((5885/2048),(1605/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2041_ok T2056_ok
def T2039 : Node := Node.split 1 T2040 T2057
theorem T2039_ok : Node.check D_R11111 T2039 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2040_ok T2057_ok
def T2038 : Node := Node.leaf L2038
theorem T2038_ok : Node.check D_R11111 T2038 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2038_ok
def T2037 : Node := Node.split 3 T2038 T2039
theorem T2037_ok : Node.check D_R11111 T2037 [((5885/2048),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2038_ok T2039_ok
def T2036 : Node := Node.leaf L2036
theorem T2036_ok : Node.check D_R11111 T2036 [((2675/1024),(5885/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2036_ok
def T2035 : Node := Node.leaf L2035
theorem T2035_ok : Node.check D_R11111 T2035 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2035_ok
def T2034 : Node := Node.leaf L2034
theorem T2034_ok : Node.check D_R11111 T2034 [((11235/4096),(5885/2048)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2034_ok
def T2033 : Node := Node.leaf L2033
theorem T2033_ok : Node.check D_R11111 T2033 [((11235/4096),(5885/2048)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2033_ok
def T2032 : Node := Node.split 1 T2033 T2034
theorem T2032_ok : Node.check D_R11111 T2032 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2033_ok T2034_ok
def T2031 : Node := Node.leaf L2031
theorem T2031_ok : Node.check D_R11111 T2031 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L2031_ok
def T2030 : Node := Node.split 3 T2031 T2032
theorem T2030_ok : Node.check D_R11111 T2030 [((11235/4096),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2031_ok T2032_ok
def T2029 : Node := Node.leaf L2029
theorem T2029_ok : Node.check D_R11111 T2029 [((2675/1024),(11235/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2029_ok
def T2028 : Node := Node.split 0 T2029 T2030
theorem T2028_ok : Node.check D_R11111 T2028 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2029_ok T2030_ok
def T2027 : Node := Node.split 2 T2028 T2035
theorem T2027_ok : Node.check D_R11111 T2027 [((2675/1024),(5885/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2028_ok T2035_ok
def T2026 : Node := Node.split 1 T2027 T2036
theorem T2026_ok : Node.check D_R11111 T2026 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2027_ok T2036_ok
def T2025 : Node := Node.leaf L2025
theorem T2025_ok : Node.check D_R11111 T2025 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L2025_ok
def T2024 : Node := Node.split 3 T2025 T2026
theorem T2024_ok : Node.check D_R11111 T2024 [((2675/1024),(5885/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2025_ok T2026_ok
def T2023 : Node := Node.split 0 T2024 T2037
theorem T2023_ok : Node.check D_R11111 T2023 [((2675/1024),(1605/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2024_ok T2037_ok
def T2022 : Node := Node.leaf L2022
theorem T2022_ok : Node.check D_R11111 T2022 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2022_ok
def T2021 : Node := Node.split 2 T2022 T2023
theorem T2021_ok : Node.check D_R11111 T2021 [((2675/1024),(1605/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2022_ok T2023_ok
def T2020 : Node := Node.leaf L2020
theorem T2020_ok : Node.check D_R11111 T2020 [((2675/1024),(1605/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2020_ok
def T2019 : Node := Node.split 1 T2020 T2021
theorem T2019_ok : Node.check D_R11111 T2019 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2020_ok T2021_ok
def T2018 : Node := Node.leaf L2018
theorem T2018_ok : Node.check D_R11111 T2018 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L2018_ok
def T2017 : Node := Node.split 3 T2018 T2019
theorem T2017_ok : Node.check D_R11111 T2017 [((2675/1024),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2018_ok T2019_ok
def T2016 : Node := Node.leaf L2016
theorem T2016_ok : Node.check D_R11111 T2016 [((4815/2048),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L2016_ok
def T2015 : Node := Node.leaf L2015
theorem T2015_ok : Node.check D_R11111 T2015 [((535/256),(4815/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2015_ok
def T2014 : Node := Node.leaf L2014
theorem T2014_ok : Node.check D_R11111 T2014 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2014_ok
def T2013 : Node := Node.leaf L2013
theorem T2013_ok : Node.check D_R11111 T2013 [((9095/4096),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L2013_ok
def T2012 : Node := Node.leaf L2012
theorem T2012_ok : Node.check D_R11111 T2012 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2012_ok
def T2011 : Node := Node.leaf L2011
theorem T2011_ok : Node.check D_R11111 T2011 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2011_ok
def T2010 : Node := Node.split 2 T2011 T2012
theorem T2010_ok : Node.check D_R11111 T2010 [((535/256),(9095/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2011_ok T2012_ok
def T2009 : Node := Node.leaf L2009
theorem T2009_ok : Node.check D_R11111 T2009 [((17655/8192),(9095/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2009_ok
def T2008 : Node := Node.leaf L2008
theorem T2008_ok : Node.check D_R11111 T2008 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2008_ok
def T2007 : Node := Node.split 0 T2008 T2009
theorem T2007_ok : Node.check D_R11111 T2007 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2008_ok T2009_ok
def T2006 : Node := Node.leaf L2006
theorem T2006_ok : Node.check D_R11111 T2006 [((17655/8192),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2006_ok
def T2005 : Node := Node.leaf L2005
theorem T2005_ok : Node.check D_R11111 T2005 [((535/256),(17655/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L2005_ok
def T2004 : Node := Node.split 0 T2005 T2006
theorem T2004_ok : Node.check D_R11111 T2004 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2005_ok T2006_ok
def T2003 : Node := Node.split 2 T2004 T2007
theorem T2003_ok : Node.check D_R11111 T2003 [((535/256),(9095/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2004_ok T2007_ok
def T2002 : Node := Node.split 1 T2003 T2010
theorem T2002_ok : Node.check D_R11111 T2002 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2003_ok T2010_ok
def T2001 : Node := Node.leaf L2001
theorem T2001_ok : Node.check D_R11111 T2001 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L2001_ok
def T2000 : Node := Node.split 3 T2001 T2002
theorem T2000_ok : Node.check D_R11111 T2000 [((535/256),(9095/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2001_ok T2002_ok
def T1999 : Node := Node.split 0 T2000 T2013
theorem T1999_ok : Node.check D_R11111 T1999 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2000_ok T2013_ok
def T1998 : Node := Node.split 2 T1999 T2014
theorem T1998_ok : Node.check D_R11111 T1998 [((535/256),(4815/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1999_ok T2014_ok
def T1997 : Node := Node.split 1 T1998 T2015
theorem T1997_ok : Node.check D_R11111 T1997 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1998_ok T2015_ok
def T1996 : Node := Node.leaf L1996
theorem T1996_ok : Node.check D_R11111 T1996 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L1996_ok
def T1995 : Node := Node.split 3 T1996 T1997
theorem T1995_ok : Node.check D_R11111 T1995 [((535/256),(4815/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1996_ok T1997_ok
def T1994 : Node := Node.split 0 T1995 T2016
theorem T1994_ok : Node.check D_R11111 T1994 [((535/256),(2675/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1995_ok T2016_ok
def T1993 : Node := Node.leaf L1993
theorem T1993_ok : Node.check D_R11111 T1993 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1993_ok
def T1992 : Node := Node.split 2 T1993 T1994
theorem T1992_ok : Node.check D_R11111 T1992 [((535/256),(2675/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1993_ok T1994_ok
def T1991 : Node := Node.leaf L1991
theorem T1991_ok : Node.check D_R11111 T1991 [((535/256),(2675/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1991_ok
def T1990 : Node := Node.split 1 T1991 T1992
theorem T1990_ok : Node.check D_R11111 T1990 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1991_ok T1992_ok
def T1989 : Node := Node.leaf L1989
theorem T1989_ok : Node.check D_R11111 T1989 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1989_ok
def T1988 : Node := Node.split 3 T1989 T1990
theorem T1988_ok : Node.check D_R11111 T1988 [((535/256),(2675/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1989_ok T1990_ok
def T1987 : Node := Node.split 0 T1988 T2017
theorem T1987_ok : Node.check D_R11111 T1987 [((535/256),(1605/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1988_ok T2017_ok
def T1986 : Node := Node.leaf L1986
theorem T1986_ok : Node.check D_R11111 T1986 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1986_ok
def T1985 : Node := Node.split 2 T1986 T1987
theorem T1985_ok : Node.check D_R11111 T1985 [((535/256),(1605/512)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1986_ok T1987_ok
def T1984 : Node := Node.leaf L1984
theorem T1984_ok : Node.check D_R11111 T1984 [((535/256),(1605/512)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1984_ok
def T1983 : Node := Node.split 1 T1984 T1985
theorem T1983_ok : Node.check D_R11111 T1983 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1984_ok T1985_ok
def T1982 : Node := Node.split 3 T1983 T2058
theorem T1982_ok : Node.check D_R11111 T1982 [((535/256),(1605/512)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1983_ok T2058_ok
def T1981 : Node := Node.split 0 T1982 T2175
theorem T1981_ok : Node.check D_R11111 T1981 [((535/256),(535/128)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1982_ok T2175_ok
def T1980 : Node := Node.split 2 T1981 T2262
theorem T1980_ok : Node.check D_R11111 T1980 [((535/256),(535/128)),((0),(333/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1981_ok T2262_ok
def T1979 : Node := Node.split 1 T1980 T2369
theorem T1979_ok : Node.check D_R11111 T1979 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1980_ok T2369_ok
def T1978 : Node := Node.split 3 T1979 T2528
theorem T1978_ok : Node.check D_R11111 T1978 [((535/256),(535/128)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1979_ok T2528_ok
def T1977 : Node := Node.leaf L1977
theorem T1977_ok : Node.check D_R11111 T1977 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1977_ok
def T1976 : Node := Node.leaf L1976
theorem T1976_ok : Node.check D_R11111 T1976 [((535/512),(535/256)),((999/512),(333/128)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1976_ok
def T1975 : Node := Node.leaf L1975
theorem T1975_ok : Node.check D_R11111 T1975 [((535/512),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1975_ok
def T1974 : Node := Node.leaf L1974
theorem T1974_ok : Node.check D_R11111 T1974 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1974_ok
def T1973 : Node := Node.split 2 T1974 T1975
theorem T1973_ok : Node.check D_R11111 T1973 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1974_ok T1975_ok
def T1972 : Node := Node.split 1 T1973 T1976
theorem T1972_ok : Node.check D_R11111 T1972 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1973_ok T1976_ok
def T1971 : Node := Node.split 3 T1972 T1977
theorem T1971_ok : Node.check D_R11111 T1971 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1972_ok T1977_ok
def T1970 : Node := Node.leaf L1970
theorem T1970_ok : Node.check D_R11111 T1970 [((0),(535/512)),((999/512),(333/128)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1970_ok
def T1969 : Node := Node.leaf L1969
theorem T1969_ok : Node.check D_R11111 T1969 [((0),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1969_ok
def T1968 : Node := Node.leaf L1968
theorem T1968_ok : Node.check D_R11111 T1968 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1968_ok
def T1967 : Node := Node.leaf L1967
theorem T1967_ok : Node.check D_R11111 T1967 [((0),(535/1024)),((333/256),(999/512)),((333/256),(999/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1967_ok
def T1966 : Node := Node.split 0 T1967 T1968
theorem T1966_ok : Node.check D_R11111 T1966 [((0),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1967_ok T1968_ok
def T1965 : Node := Node.split 2 T1966 T1969
theorem T1965_ok : Node.check D_R11111 T1965 [((0),(535/512)),((333/256),(999/512)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1966_ok T1969_ok
def T1964 : Node := Node.split 1 T1965 T1970
theorem T1964_ok : Node.check D_R11111 T1964 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1965_ok T1970_ok
def T1963 : Node := Node.leaf L1963
theorem T1963_ok : Node.check D_R11111 T1963 [((0),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1963_ok
def T1962 : Node := Node.leaf L1962
theorem T1962_ok : Node.check D_R11111 T1962 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1962_ok
def T1961 : Node := Node.leaf L1961
theorem T1961_ok : Node.check D_R11111 T1961 [((0),(535/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1961_ok
def T1960 : Node := Node.split 0 T1961 T1962
theorem T1960_ok : Node.check D_R11111 T1960 [((0),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1961_ok T1962_ok
def T1959 : Node := Node.split 2 T1960 T1963
theorem T1959_ok : Node.check D_R11111 T1959 [((0),(535/512)),((999/512),(333/128)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1960_ok T1963_ok
def T1958 : Node := Node.leaf L1958
theorem T1958_ok : Node.check D_R11111 T1958 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1958_ok
def T1957 : Node := Node.leaf L1957
theorem T1957_ok : Node.check D_R11111 T1957 [((0),(535/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1957_ok
def T1956 : Node := Node.split 0 T1957 T1958
theorem T1956_ok : Node.check D_R11111 T1956 [((0),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1957_ok T1958_ok
def T1955 : Node := Node.leaf L1955
theorem T1955_ok : Node.check D_R11111 T1955 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1955_ok
def T1954 : Node := Node.leaf L1954
theorem T1954_ok : Node.check D_R11111 T1954 [((0),(535/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1954_ok
def T1953 : Node := Node.split 0 T1954 T1955
theorem T1953_ok : Node.check D_R11111 T1953 [((0),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1954_ok T1955_ok
def T1952 : Node := Node.split 2 T1953 T1956
theorem T1952_ok : Node.check D_R11111 T1952 [((0),(535/512)),((333/256),(999/512)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1953_ok T1956_ok
def T1951 : Node := Node.split 1 T1952 T1959
theorem T1951_ok : Node.check D_R11111 T1951 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1952_ok T1959_ok
def T1950 : Node := Node.split 3 T1951 T1964
theorem T1950_ok : Node.check D_R11111 T1950 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1951_ok T1964_ok
def T1949 : Node := Node.split 0 T1950 T1971
theorem T1949_ok : Node.check D_R11111 T1949 [((0),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1950_ok T1971_ok
def T1948 : Node := Node.leaf L1948
theorem T1948_ok : Node.check D_R11111 T1948 [((535/512),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1948_ok
def T1947 : Node := Node.leaf L1947
theorem T1947_ok : Node.check D_R11111 T1947 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1947_ok
def T1946 : Node := Node.split 2 T1947 T1948
theorem T1946_ok : Node.check D_R11111 T1946 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1947_ok T1948_ok
def T1945 : Node := Node.leaf L1945
theorem T1945_ok : Node.check D_R11111 T1945 [((535/512),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1945_ok
def T1944 : Node := Node.leaf L1944
theorem T1944_ok : Node.check D_R11111 T1944 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1944_ok
def T1943 : Node := Node.split 2 T1944 T1945
theorem T1943_ok : Node.check D_R11111 T1943 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1944_ok T1945_ok
def T1942 : Node := Node.split 1 T1943 T1946
theorem T1942_ok : Node.check D_R11111 T1942 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1943_ok T1946_ok
def T1941 : Node := Node.leaf L1941
theorem T1941_ok : Node.check D_R11111 T1941 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1941_ok
def T1940 : Node := Node.leaf L1940
theorem T1940_ok : Node.check D_R11111 T1940 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1940_ok
def T1939 : Node := Node.leaf L1939
theorem T1939_ok : Node.check D_R11111 T1939 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1939_ok
def T1938 : Node := Node.leaf L1938
theorem T1938_ok : Node.check D_R11111 T1938 [((2675/2048),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1938_ok
def T1937 : Node := Node.leaf L1937
theorem T1937_ok : Node.check D_R11111 T1937 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1937_ok
def T1936 : Node := Node.leaf L1936
theorem T1936_ok : Node.check D_R11111 T1936 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1936_ok
def T1935 : Node := Node.leaf L1935
theorem T1935_ok : Node.check D_R11111 T1935 [((535/512),(2675/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1935_ok
def T1934 : Node := Node.leaf L1934
theorem T1934_ok : Node.check D_R11111 T1934 [((4815/4096),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1934_ok
def T1933 : Node := Node.leaf L1933
theorem T1933_ok : Node.check D_R11111 T1933 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1933_ok
def T1932 : Node := Node.leaf L1932
theorem T1932_ok : Node.check D_R11111 T1932 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1932_ok
def T1931 : Node := Node.leaf L1931
theorem T1931_ok : Node.check D_R11111 T1931 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1931_ok
def T1930 : Node := Node.split 1 T1931 T1932
theorem T1930_ok : Node.check D_R11111 T1930 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1931_ok T1932_ok
def T1929 : Node := Node.split 3 T1930 T1933
theorem T1929_ok : Node.check D_R11111 T1929 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1930_ok T1933_ok
def T1928 : Node := Node.split 0 T1929 T1934
theorem T1928_ok : Node.check D_R11111 T1928 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1929_ok T1934_ok
def T1927 : Node := Node.split 2 T1928 T1935
theorem T1927_ok : Node.check D_R11111 T1927 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1928_ok T1935_ok
def T1926 : Node := Node.split 1 T1927 T1936
theorem T1926_ok : Node.check D_R11111 T1926 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1927_ok T1936_ok
def T1925 : Node := Node.split 3 T1926 T1937
theorem T1925_ok : Node.check D_R11111 T1925 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1926_ok T1937_ok
def T1924 : Node := Node.split 0 T1925 T1938
theorem T1924_ok : Node.check D_R11111 T1924 [((535/512),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1925_ok T1938_ok
def T1923 : Node := Node.leaf L1923
theorem T1923_ok : Node.check D_R11111 T1923 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1923_ok
def T1922 : Node := Node.split 2 T1923 T1924
theorem T1922_ok : Node.check D_R11111 T1922 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1923_ok T1924_ok
def T1921 : Node := Node.split 1 T1922 T1939
theorem T1921_ok : Node.check D_R11111 T1921 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1922_ok T1939_ok
def T1920 : Node := Node.split 3 T1921 T1940
theorem T1920_ok : Node.check D_R11111 T1920 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1921_ok T1940_ok
def T1919 : Node := Node.split 0 T1920 T1941
theorem T1919_ok : Node.check D_R11111 T1919 [((535/512),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1920_ok T1941_ok
def T1918 : Node := Node.leaf L1918
theorem T1918_ok : Node.check D_R11111 T1918 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1918_ok
def T1917 : Node := Node.split 2 T1918 T1919
theorem T1917_ok : Node.check D_R11111 T1917 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1918_ok T1919_ok
def T1916 : Node := Node.leaf L1916
theorem T1916_ok : Node.check D_R11111 T1916 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1916_ok
def T1915 : Node := Node.leaf L1915
theorem T1915_ok : Node.check D_R11111 T1915 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1915_ok
def T1914 : Node := Node.leaf L1914
theorem T1914_ok : Node.check D_R11111 T1914 [((1605/1024),(535/256)),((333/256),(1665/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1914_ok
def T1913 : Node := Node.split 1 T1914 T1915
theorem T1913_ok : Node.check D_R11111 T1913 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1914_ok T1915_ok
def T1912 : Node := Node.split 3 T1913 T1916
theorem T1912_ok : Node.check D_R11111 T1912 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1913_ok T1916_ok
def T1911 : Node := Node.leaf L1911
theorem T1911_ok : Node.check D_R11111 T1911 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1911_ok
def T1910 : Node := Node.leaf L1910
theorem T1910_ok : Node.check D_R11111 T1910 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1910_ok
def T1909 : Node := Node.split 1 T1910 T1911
theorem T1909_ok : Node.check D_R11111 T1909 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1910_ok T1911_ok
def T1908 : Node := Node.leaf L1908
theorem T1908_ok : Node.check D_R11111 T1908 [((2675/2048),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1908_ok
def T1907 : Node := Node.leaf L1907
theorem T1907_ok : Node.check D_R11111 T1907 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1907_ok
def T1906 : Node := Node.leaf L1906
theorem T1906_ok : Node.check D_R11111 T1906 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1906_ok
def T1905 : Node := Node.leaf L1905
theorem T1905_ok : Node.check D_R11111 T1905 [((535/512),(2675/2048)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1905_ok
def T1904 : Node := Node.split 1 T1905 T1906
theorem T1904_ok : Node.check D_R11111 T1904 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1905_ok T1906_ok
def T1903 : Node := Node.split 3 T1904 T1907
theorem T1903_ok : Node.check D_R11111 T1903 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1904_ok T1907_ok
def T1902 : Node := Node.split 0 T1903 T1908
theorem T1902_ok : Node.check D_R11111 T1902 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1903_ok T1908_ok
def T1901 : Node := Node.leaf L1901
theorem T1901_ok : Node.check D_R11111 T1901 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1901_ok
def T1900 : Node := Node.split 2 T1901 T1902
theorem T1900_ok : Node.check D_R11111 T1900 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1901_ok T1902_ok
def T1899 : Node := Node.leaf L1899
theorem T1899_ok : Node.check D_R11111 T1899 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1899_ok
def T1898 : Node := Node.split 1 T1899 T1900
theorem T1898_ok : Node.check D_R11111 T1898 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1899_ok T1900_ok
def T1897 : Node := Node.split 3 T1898 T1909
theorem T1897_ok : Node.check D_R11111 T1897 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1898_ok T1909_ok
def T1896 : Node := Node.split 0 T1897 T1912
theorem T1896_ok : Node.check D_R11111 T1896 [((535/512),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1897_ok T1912_ok
def T1895 : Node := Node.leaf L1895
theorem T1895_ok : Node.check D_R11111 T1895 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1895_ok
def T1894 : Node := Node.split 2 T1895 T1896
theorem T1894_ok : Node.check D_R11111 T1894 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1895_ok T1896_ok
def T1893 : Node := Node.split 1 T1894 T1917
theorem T1893_ok : Node.check D_R11111 T1893 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1894_ok T1917_ok
def T1892 : Node := Node.split 3 T1893 T1942
theorem T1892_ok : Node.check D_R11111 T1892 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1893_ok T1942_ok
def T1891 : Node := Node.leaf L1891
theorem T1891_ok : Node.check D_R11111 T1891 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1891_ok
def T1890 : Node := Node.leaf L1890
theorem T1890_ok : Node.check D_R11111 T1890 [((0),(535/1024)),((999/512),(333/128)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1890_ok
def T1889 : Node := Node.split 0 T1890 T1891
theorem T1889_ok : Node.check D_R11111 T1889 [((0),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1890_ok T1891_ok
def T1888 : Node := Node.leaf L1888
theorem T1888_ok : Node.check D_R11111 T1888 [((0),(535/512)),((999/512),(333/128)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1888_ok
def T1887 : Node := Node.split 2 T1888 T1889
theorem T1887_ok : Node.check D_R11111 T1887 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1888_ok T1889_ok
def T1886 : Node := Node.leaf L1886
theorem T1886_ok : Node.check D_R11111 T1886 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1886_ok
def T1885 : Node := Node.leaf L1885
theorem T1885_ok : Node.check D_R11111 T1885 [((0),(535/1024)),((333/256),(999/512)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1885_ok
def T1884 : Node := Node.split 0 T1885 T1886
theorem T1884_ok : Node.check D_R11111 T1884 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1885_ok T1886_ok
def T1883 : Node := Node.leaf L1883
theorem T1883_ok : Node.check D_R11111 T1883 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1883_ok
def T1882 : Node := Node.split 2 T1883 T1884
theorem T1882_ok : Node.check D_R11111 T1882 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1883_ok T1884_ok
def T1881 : Node := Node.split 1 T1882 T1887
theorem T1881_ok : Node.check D_R11111 T1881 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1882_ok T1887_ok
def T1880 : Node := Node.leaf L1880
theorem T1880_ok : Node.check D_R11111 T1880 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1880_ok
def T1879 : Node := Node.leaf L1879
theorem T1879_ok : Node.check D_R11111 T1879 [((535/1024),(535/512)),((2331/1024),(333/128)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1879_ok
def T1878 : Node := Node.leaf L1878
theorem T1878_ok : Node.check D_R11111 T1878 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1878_ok
def T1877 : Node := Node.leaf L1877
theorem T1877_ok : Node.check D_R11111 T1877 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1877_ok
def T1876 : Node := Node.leaf L1876
theorem T1876_ok : Node.check D_R11111 T1876 [((1605/2048),(535/512)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1876_ok
def T1875 : Node := Node.leaf L1875
theorem T1875_ok : Node.check D_R11111 T1875 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1875_ok
def T1874 : Node := Node.split 2 T1875 T1876
theorem T1874_ok : Node.check D_R11111 T1874 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1875_ok T1876_ok
def T1873 : Node := Node.split 1 T1874 T1877
theorem T1873_ok : Node.check D_R11111 T1873 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1874_ok T1877_ok
def T1872 : Node := Node.split 3 T1873 T1878
theorem T1872_ok : Node.check D_R11111 T1872 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1873_ok T1878_ok
def T1871 : Node := Node.leaf L1871
theorem T1871_ok : Node.check D_R11111 T1871 [((535/1024),(1605/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1871_ok
def T1870 : Node := Node.split 0 T1871 T1872
theorem T1870_ok : Node.check D_R11111 T1870 [((535/1024),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1871_ok T1872_ok
def T1869 : Node := Node.leaf L1869
theorem T1869_ok : Node.check D_R11111 T1869 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1869_ok
def T1868 : Node := Node.split 2 T1869 T1870
theorem T1868_ok : Node.check D_R11111 T1868 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1869_ok T1870_ok
def T1867 : Node := Node.split 1 T1868 T1879
theorem T1867_ok : Node.check D_R11111 T1867 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1868_ok T1879_ok
def T1866 : Node := Node.split 3 T1867 T1880
theorem T1866_ok : Node.check D_R11111 T1866 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1867_ok T1880_ok
def T1865 : Node := Node.leaf L1865
theorem T1865_ok : Node.check D_R11111 T1865 [((0),(535/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1865_ok
def T1864 : Node := Node.split 0 T1865 T1866
theorem T1864_ok : Node.check D_R11111 T1864 [((0),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1865_ok T1866_ok
def T1863 : Node := Node.leaf L1863
theorem T1863_ok : Node.check D_R11111 T1863 [((0),(535/512)),((999/512),(333/128)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1863_ok
def T1862 : Node := Node.split 2 T1863 T1864
theorem T1862_ok : Node.check D_R11111 T1862 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1863_ok T1864_ok
def T1861 : Node := Node.leaf L1861
theorem T1861_ok : Node.check D_R11111 T1861 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1861_ok
def T1860 : Node := Node.leaf L1860
theorem T1860_ok : Node.check D_R11111 T1860 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1860_ok
def T1859 : Node := Node.leaf L1859
theorem T1859_ok : Node.check D_R11111 T1859 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1859_ok
def T1858 : Node := Node.split 1 T1859 T1860
theorem T1858_ok : Node.check D_R11111 T1858 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1859_ok T1860_ok
def T1857 : Node := Node.split 3 T1858 T1861
theorem T1857_ok : Node.check D_R11111 T1857 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1858_ok T1861_ok
def T1856 : Node := Node.leaf L1856
theorem T1856_ok : Node.check D_R11111 T1856 [((0),(535/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1856_ok
def T1855 : Node := Node.split 0 T1856 T1857
theorem T1855_ok : Node.check D_R11111 T1855 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1856_ok T1857_ok
def T1854 : Node := Node.leaf L1854
theorem T1854_ok : Node.check D_R11111 T1854 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1854_ok
def T1853 : Node := Node.split 2 T1854 T1855
theorem T1853_ok : Node.check D_R11111 T1853 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1854_ok T1855_ok
def T1852 : Node := Node.split 1 T1853 T1862
theorem T1852_ok : Node.check D_R11111 T1852 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1853_ok T1862_ok
def T1851 : Node := Node.split 3 T1852 T1881
theorem T1851_ok : Node.check D_R11111 T1851 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1852_ok T1881_ok
def T1850 : Node := Node.split 0 T1851 T1892
theorem T1850_ok : Node.check D_R11111 T1850 [((0),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1851_ok T1892_ok
def T1849 : Node := Node.split 2 T1850 T1949
theorem T1849_ok : Node.check D_R11111 T1849 [((0),(535/256)),((333/256),(333/128)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1850_ok T1949_ok
def T1848 : Node := Node.leaf L1848
theorem T1848_ok : Node.check D_R11111 T1848 [((535/512),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1848_ok
def T1847 : Node := Node.leaf L1847
theorem T1847_ok : Node.check D_R11111 T1847 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1847_ok
def T1846 : Node := Node.split 2 T1847 T1848
theorem T1846_ok : Node.check D_R11111 T1846 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1847_ok T1848_ok
def T1845 : Node := Node.leaf L1845
theorem T1845_ok : Node.check D_R11111 T1845 [((535/512),(535/256)),((0),(333/512)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1845_ok
def T1844 : Node := Node.split 1 T1845 T1846
theorem T1844_ok : Node.check D_R11111 T1844 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1845_ok T1846_ok
def T1843 : Node := Node.leaf L1843
theorem T1843_ok : Node.check D_R11111 T1843 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1843_ok
def T1842 : Node := Node.leaf L1842
theorem T1842_ok : Node.check D_R11111 T1842 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1842_ok
def T1841 : Node := Node.leaf L1841
theorem T1841_ok : Node.check D_R11111 T1841 [((535/512),(1605/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1841_ok
def T1840 : Node := Node.leaf L1840
theorem T1840_ok : Node.check D_R11111 T1840 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1840_ok
def T1839 : Node := Node.leaf L1839
theorem T1839_ok : Node.check D_R11111 T1839 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1839_ok
def T1838 : Node := Node.leaf L1838
theorem T1838_ok : Node.check D_R11111 T1838 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1838_ok
def T1837 : Node := Node.leaf L1837
theorem T1837_ok : Node.check D_R11111 T1837 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1837_ok
def T1836 : Node := Node.leaf L1836
theorem T1836_ok : Node.check D_R11111 T1836 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1836_ok
def T1835 : Node := Node.leaf L1835
theorem T1835_ok : Node.check D_R11111 T1835 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1835_ok
def T1834 : Node := Node.leaf L1834
theorem T1834_ok : Node.check D_R11111 T1834 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1834_ok
def T1833 : Node := Node.leaf L1833
theorem T1833_ok : Node.check D_R11111 T1833 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1833_ok
def T1832 : Node := Node.split 1 T1833 T1834
theorem T1832_ok : Node.check D_R11111 T1832 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1833_ok T1834_ok
def T1831 : Node := Node.split 3 T1832 T1835
theorem T1831_ok : Node.check D_R11111 T1831 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1832_ok T1835_ok
def T1830 : Node := Node.split 0 T1831 T1836
theorem T1830_ok : Node.check D_R11111 T1830 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1831_ok T1836_ok
def T1829 : Node := Node.split 2 T1830 T1837
theorem T1829_ok : Node.check D_R11111 T1829 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1830_ok T1837_ok
def T1828 : Node := Node.split 1 T1829 T1838
theorem T1828_ok : Node.check D_R11111 T1828 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1829_ok T1838_ok
def T1827 : Node := Node.split 3 T1828 T1839
theorem T1827_ok : Node.check D_R11111 T1827 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1828_ok T1839_ok
def T1826 : Node := Node.split 0 T1827 T1840
theorem T1826_ok : Node.check D_R11111 T1826 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1827_ok T1840_ok
def T1825 : Node := Node.split 2 T1826 T1841
theorem T1825_ok : Node.check D_R11111 T1825 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(333/128)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1826_ok T1841_ok
def T1824 : Node := Node.leaf L1824
theorem T1824_ok : Node.check D_R11111 T1824 [((535/512),(1605/1024)),((333/512),(999/1024)),((999/512),(333/128)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1824_ok
def T1823 : Node := Node.split 1 T1824 T1825
theorem T1823_ok : Node.check D_R11111 T1823 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1824_ok T1825_ok
def T1822 : Node := Node.split 3 T1823 T1842
theorem T1822_ok : Node.check D_R11111 T1822 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1823_ok T1842_ok
def T1821 : Node := Node.split 0 T1822 T1843
theorem T1821_ok : Node.check D_R11111 T1821 [((535/512),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1822_ok T1843_ok
def T1820 : Node := Node.leaf L1820
theorem T1820_ok : Node.check D_R11111 T1820 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1820_ok
def T1819 : Node := Node.leaf L1819
theorem T1819_ok : Node.check D_R11111 T1819 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1819_ok
def T1818 : Node := Node.leaf L1818
theorem T1818_ok : Node.check D_R11111 T1818 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/256),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1818_ok
def T1817 : Node := Node.split 1 T1818 T1819
theorem T1817_ok : Node.check D_R11111 T1817 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1818_ok T1819_ok
def T1816 : Node := Node.split 3 T1817 T1820
theorem T1816_ok : Node.check D_R11111 T1816 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1817_ok T1820_ok
def T1815 : Node := Node.leaf L1815
theorem T1815_ok : Node.check D_R11111 T1815 [((535/512),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1815_ok
def T1814 : Node := Node.leaf L1814
theorem T1814_ok : Node.check D_R11111 T1814 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1814_ok
def T1813 : Node := Node.split 2 T1814 T1815
theorem T1813_ok : Node.check D_R11111 T1813 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(999/512)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1814_ok T1815_ok
def T1812 : Node := Node.leaf L1812
theorem T1812_ok : Node.check D_R11111 T1812 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/256),(999/512)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1812_ok
def T1811 : Node := Node.split 1 T1812 T1813
theorem T1811_ok : Node.check D_R11111 T1811 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1812_ok T1813_ok
def T1810 : Node := Node.leaf L1810
theorem T1810_ok : Node.check D_R11111 T1810 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1810_ok
def T1809 : Node := Node.leaf L1809
theorem T1809_ok : Node.check D_R11111 T1809 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1809_ok
def T1808 : Node := Node.leaf L1808
theorem T1808_ok : Node.check D_R11111 T1808 [((535/512),(2675/2048)),((2331/2048),(333/256)),((1665/1024),(999/512)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1808_ok
def T1807 : Node := Node.leaf L1807
theorem T1807_ok : Node.check D_R11111 T1807 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1807_ok
def T1806 : Node := Node.split 1 T1807 T1808
theorem T1806_ok : Node.check D_R11111 T1806 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1807_ok T1808_ok
def T1805 : Node := Node.split 3 T1806 T1809
theorem T1805_ok : Node.check D_R11111 T1805 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1806_ok T1809_ok
def T1804 : Node := Node.split 0 T1805 T1810
theorem T1804_ok : Node.check D_R11111 T1804 [((535/512),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1805_ok T1810_ok
def T1803 : Node := Node.leaf L1803
theorem T1803_ok : Node.check D_R11111 T1803 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1803_ok
def T1802 : Node := Node.split 2 T1803 T1804
theorem T1802_ok : Node.check D_R11111 T1802 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1803_ok T1804_ok
def T1801 : Node := Node.leaf L1801
theorem T1801_ok : Node.check D_R11111 T1801 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/256),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1801_ok
def T1800 : Node := Node.split 1 T1801 T1802
theorem T1800_ok : Node.check D_R11111 T1800 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1801_ok T1802_ok
def T1799 : Node := Node.split 3 T1800 T1811
theorem T1799_ok : Node.check D_R11111 T1799 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1800_ok T1811_ok
def T1798 : Node := Node.split 0 T1799 T1816
theorem T1798_ok : Node.check D_R11111 T1798 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1799_ok T1816_ok
def T1797 : Node := Node.split 2 T1798 T1821
theorem T1797_ok : Node.check D_R11111 T1797 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1798_ok T1821_ok
def T1796 : Node := Node.leaf L1796
theorem T1796_ok : Node.check D_R11111 T1796 [((535/512),(535/256)),((0),(333/512)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1796_ok
def T1795 : Node := Node.split 1 T1796 T1797
theorem T1795_ok : Node.check D_R11111 T1795 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1796_ok T1797_ok
def T1794 : Node := Node.split 3 T1795 T1844
theorem T1794_ok : Node.check D_R11111 T1794 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1795_ok T1844_ok
def T1793 : Node := Node.leaf L1793
theorem T1793_ok : Node.check D_R11111 T1793 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1793_ok
def T1792 : Node := Node.leaf L1792
theorem T1792_ok : Node.check D_R11111 T1792 [((0),(535/1024)),((333/512),(333/256)),((999/512),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1792_ok
def T1791 : Node := Node.split 0 T1792 T1793
theorem T1791_ok : Node.check D_R11111 T1791 [((0),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1792_ok T1793_ok
def T1790 : Node := Node.leaf L1790
theorem T1790_ok : Node.check D_R11111 T1790 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1790_ok
def T1789 : Node := Node.leaf L1789
theorem T1789_ok : Node.check D_R11111 T1789 [((0),(535/1024)),((333/512),(333/256)),((333/256),(999/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1789_ok
def T1788 : Node := Node.split 0 T1789 T1790
theorem T1788_ok : Node.check D_R11111 T1788 [((0),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1789_ok T1790_ok
def T1787 : Node := Node.split 2 T1788 T1791
theorem T1787_ok : Node.check D_R11111 T1787 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1788_ok T1791_ok
def T1786 : Node := Node.leaf L1786
theorem T1786_ok : Node.check D_R11111 T1786 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1786_ok
def T1785 : Node := Node.split 1 T1786 T1787
theorem T1785_ok : Node.check D_R11111 T1785 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1786_ok T1787_ok
def T1784 : Node := Node.leaf L1784
theorem T1784_ok : Node.check D_R11111 T1784 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1784_ok
def T1783 : Node := Node.leaf L1783
theorem T1783_ok : Node.check D_R11111 T1783 [((535/1024),(535/512)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1783_ok
def T1782 : Node := Node.leaf L1782
theorem T1782_ok : Node.check D_R11111 T1782 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1782_ok
def T1781 : Node := Node.leaf L1781
theorem T1781_ok : Node.check D_R11111 T1781 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1781_ok
def T1780 : Node := Node.leaf L1780
theorem T1780_ok : Node.check D_R11111 T1780 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1780_ok
def T1779 : Node := Node.split 1 T1780 T1781
theorem T1779_ok : Node.check D_R11111 T1779 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1780_ok T1781_ok
def T1778 : Node := Node.split 3 T1779 T1782
theorem T1778_ok : Node.check D_R11111 T1778 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1779_ok T1782_ok
def T1777 : Node := Node.leaf L1777
theorem T1777_ok : Node.check D_R11111 T1777 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1777_ok
def T1776 : Node := Node.split 0 T1777 T1778
theorem T1776_ok : Node.check D_R11111 T1776 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1777_ok T1778_ok
def T1775 : Node := Node.split 2 T1776 T1783
theorem T1775_ok : Node.check D_R11111 T1775 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(333/128)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1776_ok T1783_ok
def T1774 : Node := Node.leaf L1774
theorem T1774_ok : Node.check D_R11111 T1774 [((535/1024),(535/512)),((333/512),(999/1024)),((999/512),(333/128)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1774_ok
def T1773 : Node := Node.split 1 T1774 T1775
theorem T1773_ok : Node.check D_R11111 T1773 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1774_ok T1775_ok
def T1772 : Node := Node.split 3 T1773 T1784
theorem T1772_ok : Node.check D_R11111 T1772 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1773_ok T1784_ok
def T1771 : Node := Node.leaf L1771
theorem T1771_ok : Node.check D_R11111 T1771 [((0),(535/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1771_ok
def T1770 : Node := Node.split 0 T1771 T1772
theorem T1770_ok : Node.check D_R11111 T1770 [((0),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1771_ok T1772_ok
def T1769 : Node := Node.leaf L1769
theorem T1769_ok : Node.check D_R11111 T1769 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1769_ok
def T1768 : Node := Node.leaf L1768
theorem T1768_ok : Node.check D_R11111 T1768 [((535/1024),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1768_ok
def T1767 : Node := Node.leaf L1767
theorem T1767_ok : Node.check D_R11111 T1767 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1767_ok
def T1766 : Node := Node.split 2 T1767 T1768
theorem T1766_ok : Node.check D_R11111 T1766 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1767_ok T1768_ok
def T1765 : Node := Node.leaf L1765
theorem T1765_ok : Node.check D_R11111 T1765 [((535/1024),(535/512)),((333/512),(999/1024)),((333/256),(999/512)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1765_ok
def T1764 : Node := Node.split 1 T1765 T1766
theorem T1764_ok : Node.check D_R11111 T1764 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1765_ok T1766_ok
def T1763 : Node := Node.split 3 T1764 T1769
theorem T1763_ok : Node.check D_R11111 T1763 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1764_ok T1769_ok
def T1762 : Node := Node.leaf L1762
theorem T1762_ok : Node.check D_R11111 T1762 [((0),(535/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1762_ok
def T1761 : Node := Node.split 0 T1762 T1763
theorem T1761_ok : Node.check D_R11111 T1761 [((0),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1762_ok T1763_ok
def T1760 : Node := Node.split 2 T1761 T1770
theorem T1760_ok : Node.check D_R11111 T1760 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1761_ok T1770_ok
def T1759 : Node := Node.leaf L1759
theorem T1759_ok : Node.check D_R11111 T1759 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1759_ok
def T1758 : Node := Node.split 1 T1759 T1760
theorem T1758_ok : Node.check D_R11111 T1758 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1759_ok T1760_ok
def T1757 : Node := Node.split 3 T1758 T1785
theorem T1757_ok : Node.check D_R11111 T1757 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1758_ok T1785_ok
def T1756 : Node := Node.split 0 T1757 T1794
theorem T1756_ok : Node.check D_R11111 T1756 [((0),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1757_ok T1794_ok
def T1755 : Node := Node.leaf L1755
theorem T1755_ok : Node.check D_R11111 T1755 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1755_ok
def T1754 : Node := Node.leaf L1754
theorem T1754_ok : Node.check D_R11111 T1754 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1754_ok
def T1753 : Node := Node.leaf L1753
theorem T1753_ok : Node.check D_R11111 T1753 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1753_ok
def T1752 : Node := Node.split 0 T1753 T1754
theorem T1752_ok : Node.check D_R11111 T1752 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1753_ok T1754_ok
def T1751 : Node := Node.leaf L1751
theorem T1751_ok : Node.check D_R11111 T1751 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1751_ok
def T1750 : Node := Node.split 2 T1751 T1752
theorem T1750_ok : Node.check D_R11111 T1750 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1751_ok T1752_ok
def T1749 : Node := Node.leaf L1749
theorem T1749_ok : Node.check D_R11111 T1749 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1749_ok
def T1748 : Node := Node.split 1 T1749 T1750
theorem T1748_ok : Node.check D_R11111 T1748 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1749_ok T1750_ok
def T1747 : Node := Node.split 3 T1748 T1755
theorem T1747_ok : Node.check D_R11111 T1747 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1748_ok T1755_ok
def T1746 : Node := Node.leaf L1746
theorem T1746_ok : Node.check D_R11111 T1746 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1746_ok
def T1745 : Node := Node.leaf L1745
theorem T1745_ok : Node.check D_R11111 T1745 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((8025/2048),(535/128))] = true := Node.check_leaf_of _ _ _ L1745_ok
def T1744 : Node := Node.leaf L1744
theorem T1744_ok : Node.check D_R11111 T1744 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((8025/2048),(535/128))] = true := Node.check_leaf_of _ _ _ L1744_ok
def T1743 : Node := Node.leaf L1743
theorem T1743_ok : Node.check D_R11111 T1743 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/2048),(535/128))] = true := Node.check_leaf_of _ _ _ L1743_ok
def T1742 : Node := Node.split 2 T1743 T1744
theorem T1742_ok : Node.check D_R11111 T1742 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((8025/2048),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1743_ok T1744_ok
def T1741 : Node := Node.split 1 T1742 T1745
theorem T1741_ok : Node.check D_R11111 T1741 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((8025/2048),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1742_ok T1745_ok
def T1740 : Node := Node.leaf L1740
theorem T1740_ok : Node.check D_R11111 T1740 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true := Node.check_leaf_of _ _ _ L1740_ok
def T1739 : Node := Node.leaf L1739
theorem T1739_ok : Node.check D_R11111 T1739 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/1024),(8025/2048))] = true := Node.check_leaf_of _ _ _ L1739_ok
def T1738 : Node := Node.leaf L1738
theorem T1738_ok : Node.check D_R11111 T1738 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/1024),(8025/2048))] = true := Node.check_leaf_of _ _ _ L1738_ok
def T1737 : Node := Node.split 2 T1738 T1739
theorem T1737_ok : Node.check D_R11111 T1737 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1738_ok T1739_ok
def T1736 : Node := Node.split 1 T1737 T1740
theorem T1736_ok : Node.check D_R11111 T1736 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1737_ok T1740_ok
def T1735 : Node := Node.split 3 T1736 T1741
theorem T1735_ok : Node.check D_R11111 T1735 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1736_ok T1741_ok
def T1734 : Node := Node.split 0 T1735 T1746
theorem T1734_ok : Node.check D_R11111 T1734 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1735_ok T1746_ok
def T1733 : Node := Node.leaf L1733
theorem T1733_ok : Node.check D_R11111 T1733 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1733_ok
def T1732 : Node := Node.split 2 T1733 T1734
theorem T1732_ok : Node.check D_R11111 T1732 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1733_ok T1734_ok
def T1731 : Node := Node.leaf L1731
theorem T1731_ok : Node.check D_R11111 T1731 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1731_ok
def T1730 : Node := Node.split 1 T1731 T1732
theorem T1730_ok : Node.check D_R11111 T1730 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1731_ok T1732_ok
def T1729 : Node := Node.leaf L1729
theorem T1729_ok : Node.check D_R11111 T1729 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1729_ok
def T1728 : Node := Node.leaf L1728
theorem T1728_ok : Node.check D_R11111 T1728 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((6955/2048),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1728_ok
def T1727 : Node := Node.leaf L1727
theorem T1727_ok : Node.check D_R11111 T1727 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1727_ok
def T1726 : Node := Node.leaf L1726
theorem T1726_ok : Node.check D_R11111 T1726 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1726_ok
def T1725 : Node := Node.leaf L1725
theorem T1725_ok : Node.check D_R11111 T1725 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1725_ok
def T1724 : Node := Node.leaf L1724
theorem T1724_ok : Node.check D_R11111 T1724 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((13375/4096),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1724_ok
def T1723 : Node := Node.leaf L1723
theorem T1723_ok : Node.check D_R11111 T1723 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/512),(13375/4096))] = true := Node.check_leaf_of _ _ _ L1723_ok
def T1722 : Node := Node.split 3 T1723 T1724
theorem T1722_ok : Node.check D_R11111 T1722 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1723_ok T1724_ok
def T1721 : Node := Node.split 0 T1722 T1725
theorem T1721_ok : Node.check D_R11111 T1721 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1722_ok T1725_ok
def T1720 : Node := Node.split 2 T1721 T1726
theorem T1720_ok : Node.check D_R11111 T1720 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1721_ok T1726_ok
def T1719 : Node := Node.split 1 T1720 T1727
theorem T1719_ok : Node.check D_R11111 T1719 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1720_ok T1727_ok
def T1718 : Node := Node.split 3 T1719 T1728
theorem T1718_ok : Node.check D_R11111 T1718 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1719_ok T1728_ok
def T1717 : Node := Node.split 0 T1718 T1729
theorem T1717_ok : Node.check D_R11111 T1717 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1718_ok T1729_ok
def T1716 : Node := Node.leaf L1716
theorem T1716_ok : Node.check D_R11111 T1716 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1716_ok
def T1715 : Node := Node.split 2 T1716 T1717
theorem T1715_ok : Node.check D_R11111 T1715 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1716_ok T1717_ok
def T1714 : Node := Node.leaf L1714
theorem T1714_ok : Node.check D_R11111 T1714 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1714_ok
def T1713 : Node := Node.split 1 T1714 T1715
theorem T1713_ok : Node.check D_R11111 T1713 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1714_ok T1715_ok
def T1712 : Node := Node.split 3 T1713 T1730
theorem T1712_ok : Node.check D_R11111 T1712 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1713_ok T1730_ok
def T1711 : Node := Node.split 0 T1712 T1747
theorem T1711_ok : Node.check D_R11111 T1711 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1712_ok T1747_ok
def T1710 : Node := Node.leaf L1710
theorem T1710_ok : Node.check D_R11111 T1710 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1710_ok
def T1709 : Node := Node.split 2 T1710 T1711
theorem T1709_ok : Node.check D_R11111 T1709 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1710_ok T1711_ok
def T1708 : Node := Node.leaf L1708
theorem T1708_ok : Node.check D_R11111 T1708 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1708_ok
def T1707 : Node := Node.split 1 T1708 T1709
theorem T1707_ok : Node.check D_R11111 T1707 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1708_ok T1709_ok
def T1706 : Node := Node.leaf L1706
theorem T1706_ok : Node.check D_R11111 T1706 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1706_ok
def T1705 : Node := Node.leaf L1705
theorem T1705_ok : Node.check D_R11111 T1705 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1705_ok
def T1704 : Node := Node.leaf L1704
theorem T1704_ok : Node.check D_R11111 T1704 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1704_ok
def T1703 : Node := Node.split 2 T1704 T1705
theorem T1703_ok : Node.check D_R11111 T1703 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1704_ok T1705_ok
def T1702 : Node := Node.split 1 T1703 T1706
theorem T1702_ok : Node.check D_R11111 T1702 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1703_ok T1706_ok
def T1701 : Node := Node.leaf L1701
theorem T1701_ok : Node.check D_R11111 T1701 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1701_ok
def T1700 : Node := Node.split 3 T1701 T1702
theorem T1700_ok : Node.check D_R11111 T1700 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1701_ok T1702_ok
def T1699 : Node := Node.leaf L1699
theorem T1699_ok : Node.check D_R11111 T1699 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1699_ok
def T1698 : Node := Node.split 0 T1699 T1700
theorem T1698_ok : Node.check D_R11111 T1698 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1699_ok T1700_ok
def T1697 : Node := Node.leaf L1697
theorem T1697_ok : Node.check D_R11111 T1697 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1697_ok
def T1696 : Node := Node.split 2 T1697 T1698
theorem T1696_ok : Node.check D_R11111 T1696 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1697_ok T1698_ok
def T1695 : Node := Node.leaf L1695
theorem T1695_ok : Node.check D_R11111 T1695 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1695_ok
def T1694 : Node := Node.split 1 T1695 T1696
theorem T1694_ok : Node.check D_R11111 T1694 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1695_ok T1696_ok
def T1693 : Node := Node.leaf L1693
theorem T1693_ok : Node.check D_R11111 T1693 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1693_ok
def T1692 : Node := Node.leaf L1692
theorem T1692_ok : Node.check D_R11111 T1692 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1692_ok
def T1691 : Node := Node.leaf L1691
theorem T1691_ok : Node.check D_R11111 T1691 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1691_ok
def T1690 : Node := Node.leaf L1690
theorem T1690_ok : Node.check D_R11111 T1690 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1690_ok
def T1689 : Node := Node.leaf L1689
theorem T1689_ok : Node.check D_R11111 T1689 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1689_ok
def T1688 : Node := Node.leaf L1688
theorem T1688_ok : Node.check D_R11111 T1688 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1688_ok
def T1687 : Node := Node.split 2 T1688 T1689
theorem T1687_ok : Node.check D_R11111 T1687 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1688_ok T1689_ok
def T1686 : Node := Node.leaf L1686
theorem T1686_ok : Node.check D_R11111 T1686 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1686_ok
def T1685 : Node := Node.leaf L1685
theorem T1685_ok : Node.check D_R11111 T1685 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1685_ok
def T1684 : Node := Node.split 2 T1685 T1686
theorem T1684_ok : Node.check D_R11111 T1684 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1685_ok T1686_ok
def T1683 : Node := Node.split 1 T1684 T1687
theorem T1683_ok : Node.check D_R11111 T1683 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1684_ok T1687_ok
def T1682 : Node := Node.split 3 T1683 T1690
theorem T1682_ok : Node.check D_R11111 T1682 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1683_ok T1690_ok
def T1681 : Node := Node.leaf L1681
theorem T1681_ok : Node.check D_R11111 T1681 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1681_ok
def T1680 : Node := Node.leaf L1680
theorem T1680_ok : Node.check D_R11111 T1680 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1680_ok
def T1679 : Node := Node.leaf L1679
theorem T1679_ok : Node.check D_R11111 T1679 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1679_ok
def T1678 : Node := Node.split 2 T1679 T1680
theorem T1678_ok : Node.check D_R11111 T1678 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1679_ok T1680_ok
def T1677 : Node := Node.leaf L1677
theorem T1677_ok : Node.check D_R11111 T1677 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1677_ok
def T1676 : Node := Node.split 1 T1677 T1678
theorem T1676_ok : Node.check D_R11111 T1676 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1677_ok T1678_ok
def T1675 : Node := Node.split 3 T1676 T1681
theorem T1675_ok : Node.check D_R11111 T1675 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1676_ok T1681_ok
def T1674 : Node := Node.split 0 T1675 T1682
theorem T1674_ok : Node.check D_R11111 T1674 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1675_ok T1682_ok
def T1673 : Node := Node.split 2 T1674 T1691
theorem T1673_ok : Node.check D_R11111 T1673 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1674_ok T1691_ok
def T1672 : Node := Node.split 1 T1673 T1692
theorem T1672_ok : Node.check D_R11111 T1672 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1673_ok T1692_ok
def T1671 : Node := Node.split 3 T1672 T1693
theorem T1671_ok : Node.check D_R11111 T1671 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1672_ok T1693_ok
def T1670 : Node := Node.leaf L1670
theorem T1670_ok : Node.check D_R11111 T1670 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1670_ok
def T1669 : Node := Node.split 0 T1670 T1671
theorem T1669_ok : Node.check D_R11111 T1669 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1670_ok T1671_ok
def T1668 : Node := Node.leaf L1668
theorem T1668_ok : Node.check D_R11111 T1668 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1668_ok
def T1667 : Node := Node.split 2 T1668 T1669
theorem T1667_ok : Node.check D_R11111 T1667 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1668_ok T1669_ok
def T1666 : Node := Node.leaf L1666
theorem T1666_ok : Node.check D_R11111 T1666 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1666_ok
def T1665 : Node := Node.split 1 T1666 T1667
theorem T1665_ok : Node.check D_R11111 T1665 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1666_ok T1667_ok
def T1664 : Node := Node.split 3 T1665 T1694
theorem T1664_ok : Node.check D_R11111 T1664 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1665_ok T1694_ok
def T1663 : Node := Node.leaf L1663
theorem T1663_ok : Node.check D_R11111 T1663 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1663_ok
def T1662 : Node := Node.leaf L1662
theorem T1662_ok : Node.check D_R11111 T1662 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1662_ok
def T1661 : Node := Node.leaf L1661
theorem T1661_ok : Node.check D_R11111 T1661 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1661_ok
def T1660 : Node := Node.leaf L1660
theorem T1660_ok : Node.check D_R11111 T1660 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1660_ok
def T1659 : Node := Node.leaf L1659
theorem T1659_ok : Node.check D_R11111 T1659 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1659_ok
def T1658 : Node := Node.leaf L1658
theorem T1658_ok : Node.check D_R11111 T1658 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1658_ok
def T1657 : Node := Node.split 2 T1658 T1659
theorem T1657_ok : Node.check D_R11111 T1657 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1658_ok T1659_ok
def T1656 : Node := Node.leaf L1656
theorem T1656_ok : Node.check D_R11111 T1656 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1656_ok
def T1655 : Node := Node.leaf L1655
theorem T1655_ok : Node.check D_R11111 T1655 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1655_ok
def T1654 : Node := Node.split 2 T1655 T1656
theorem T1654_ok : Node.check D_R11111 T1654 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1655_ok T1656_ok
def T1653 : Node := Node.split 1 T1654 T1657
theorem T1653_ok : Node.check D_R11111 T1653 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1654_ok T1657_ok
def T1652 : Node := Node.leaf L1652
theorem T1652_ok : Node.check D_R11111 T1652 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1652_ok
def T1651 : Node := Node.leaf L1651
theorem T1651_ok : Node.check D_R11111 T1651 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1651_ok
def T1650 : Node := Node.split 2 T1651 T1652
theorem T1650_ok : Node.check D_R11111 T1650 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1651_ok T1652_ok
def T1649 : Node := Node.leaf L1649
theorem T1649_ok : Node.check D_R11111 T1649 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1649_ok
def T1648 : Node := Node.leaf L1648
theorem T1648_ok : Node.check D_R11111 T1648 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1648_ok
def T1647 : Node := Node.split 2 T1648 T1649
theorem T1647_ok : Node.check D_R11111 T1647 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1648_ok T1649_ok
def T1646 : Node := Node.split 1 T1647 T1650
theorem T1646_ok : Node.check D_R11111 T1646 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1647_ok T1650_ok
def T1645 : Node := Node.split 3 T1646 T1653
theorem T1645_ok : Node.check D_R11111 T1645 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1646_ok T1653_ok
def T1644 : Node := Node.split 0 T1645 T1660
theorem T1644_ok : Node.check D_R11111 T1644 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1645_ok T1660_ok
def T1643 : Node := Node.split 2 T1644 T1661
theorem T1643_ok : Node.check D_R11111 T1643 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1644_ok T1661_ok
def T1642 : Node := Node.split 1 T1643 T1662
theorem T1642_ok : Node.check D_R11111 T1642 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1643_ok T1662_ok
def T1641 : Node := Node.leaf L1641
theorem T1641_ok : Node.check D_R11111 T1641 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1641_ok
def T1640 : Node := Node.leaf L1640
theorem T1640_ok : Node.check D_R11111 T1640 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1640_ok
def T1639 : Node := Node.leaf L1639
theorem T1639_ok : Node.check D_R11111 T1639 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1639_ok
def T1638 : Node := Node.leaf L1638
theorem T1638_ok : Node.check D_R11111 T1638 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((11235/4096),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1638_ok
def T1637 : Node := Node.leaf L1637
theorem T1637_ok : Node.check D_R11111 T1637 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((11235/4096),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1637_ok
def T1636 : Node := Node.split 2 T1637 T1638
theorem T1636_ok : Node.check D_R11111 T1636 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1637_ok T1638_ok
def T1635 : Node := Node.leaf L1635
theorem T1635_ok : Node.check D_R11111 T1635 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1635_ok
def T1634 : Node := Node.split 1 T1635 T1636
theorem T1634_ok : Node.check D_R11111 T1634 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1635_ok T1636_ok
def T1633 : Node := Node.leaf L1633
theorem T1633_ok : Node.check D_R11111 T1633 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(11235/4096))] = true := Node.check_leaf_of _ _ _ L1633_ok
def T1632 : Node := Node.split 3 T1633 T1634
theorem T1632_ok : Node.check D_R11111 T1632 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1633_ok T1634_ok
def T1631 : Node := Node.split 0 T1632 T1639
theorem T1631_ok : Node.check D_R11111 T1631 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1632_ok T1639_ok
def T1630 : Node := Node.split 2 T1631 T1640
theorem T1630_ok : Node.check D_R11111 T1630 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1631_ok T1640_ok
def T1629 : Node := Node.split 1 T1630 T1641
theorem T1629_ok : Node.check D_R11111 T1629 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1630_ok T1641_ok
def T1628 : Node := Node.split 3 T1629 T1642
theorem T1628_ok : Node.check D_R11111 T1628 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1629_ok T1642_ok
def T1627 : Node := Node.split 0 T1628 T1663
theorem T1627_ok : Node.check D_R11111 T1627 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1628_ok T1663_ok
def T1626 : Node := Node.leaf L1626
theorem T1626_ok : Node.check D_R11111 T1626 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1626_ok
def T1625 : Node := Node.split 2 T1626 T1627
theorem T1625_ok : Node.check D_R11111 T1625 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1626_ok T1627_ok
def T1624 : Node := Node.leaf L1624
theorem T1624_ok : Node.check D_R11111 T1624 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1624_ok
def T1623 : Node := Node.split 1 T1624 T1625
theorem T1623_ok : Node.check D_R11111 T1623 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1624_ok T1625_ok
def T1622 : Node := Node.leaf L1622
theorem T1622_ok : Node.check D_R11111 T1622 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1622_ok
def T1621 : Node := Node.leaf L1621
theorem T1621_ok : Node.check D_R11111 T1621 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1621_ok
def T1620 : Node := Node.leaf L1620
theorem T1620_ok : Node.check D_R11111 T1620 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1620_ok
def T1619 : Node := Node.leaf L1619
theorem T1619_ok : Node.check D_R11111 T1619 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1619_ok
def T1618 : Node := Node.leaf L1618
theorem T1618_ok : Node.check D_R11111 T1618 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1618_ok
def T1617 : Node := Node.leaf L1617
theorem T1617_ok : Node.check D_R11111 T1617 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1617_ok
def T1616 : Node := Node.leaf L1616
theorem T1616_ok : Node.check D_R11111 T1616 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1616_ok
def T1615 : Node := Node.leaf L1615
theorem T1615_ok : Node.check D_R11111 T1615 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1615_ok
def T1614 : Node := Node.leaf L1614
theorem T1614_ok : Node.check D_R11111 T1614 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1614_ok
def T1613 : Node := Node.split 0 T1614 T1615
theorem T1613_ok : Node.check D_R11111 T1613 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1614_ok T1615_ok
def T1612 : Node := Node.split 2 T1613 T1616
theorem T1612_ok : Node.check D_R11111 T1612 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1613_ok T1616_ok
def T1611 : Node := Node.leaf L1611
theorem T1611_ok : Node.check D_R11111 T1611 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1611_ok
def T1610 : Node := Node.leaf L1610
theorem T1610_ok : Node.check D_R11111 T1610 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1610_ok
def T1609 : Node := Node.leaf L1609
theorem T1609_ok : Node.check D_R11111 T1609 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1609_ok
def T1608 : Node := Node.split 0 T1609 T1610
theorem T1608_ok : Node.check D_R11111 T1608 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1609_ok T1610_ok
def T1607 : Node := Node.split 2 T1608 T1611
theorem T1607_ok : Node.check D_R11111 T1607 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1608_ok T1611_ok
def T1606 : Node := Node.split 1 T1607 T1612
theorem T1606_ok : Node.check D_R11111 T1606 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1607_ok T1612_ok
def T1605 : Node := Node.split 3 T1606 T1617
theorem T1605_ok : Node.check D_R11111 T1605 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1606_ok T1617_ok
def T1604 : Node := Node.split 0 T1605 T1618
theorem T1604_ok : Node.check D_R11111 T1604 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1605_ok T1618_ok
def T1603 : Node := Node.split 2 T1604 T1619
theorem T1603_ok : Node.check D_R11111 T1603 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1604_ok T1619_ok
def T1602 : Node := Node.split 1 T1603 T1620
theorem T1602_ok : Node.check D_R11111 T1602 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1603_ok T1620_ok
def T1601 : Node := Node.split 3 T1602 T1621
theorem T1601_ok : Node.check D_R11111 T1601 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1602_ok T1621_ok
def T1600 : Node := Node.split 0 T1601 T1622
theorem T1600_ok : Node.check D_R11111 T1600 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1601_ok T1622_ok
def T1599 : Node := Node.leaf L1599
theorem T1599_ok : Node.check D_R11111 T1599 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1599_ok
def T1598 : Node := Node.split 2 T1599 T1600
theorem T1598_ok : Node.check D_R11111 T1598 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1599_ok T1600_ok
def T1597 : Node := Node.leaf L1597
theorem T1597_ok : Node.check D_R11111 T1597 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1597_ok
def T1596 : Node := Node.split 1 T1597 T1598
theorem T1596_ok : Node.check D_R11111 T1596 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1597_ok T1598_ok
def T1595 : Node := Node.split 3 T1596 T1623
theorem T1595_ok : Node.check D_R11111 T1595 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1596_ok T1623_ok
def T1594 : Node := Node.split 0 T1595 T1664
theorem T1594_ok : Node.check D_R11111 T1594 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1595_ok T1664_ok
def T1593 : Node := Node.leaf L1593
theorem T1593_ok : Node.check D_R11111 T1593 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1593_ok
def T1592 : Node := Node.split 2 T1593 T1594
theorem T1592_ok : Node.check D_R11111 T1592 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1593_ok T1594_ok
def T1591 : Node := Node.leaf L1591
theorem T1591_ok : Node.check D_R11111 T1591 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1591_ok
def T1590 : Node := Node.split 1 T1591 T1592
theorem T1590_ok : Node.check D_R11111 T1590 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1591_ok T1592_ok
def T1589 : Node := Node.split 3 T1590 T1707
theorem T1589_ok : Node.check D_R11111 T1589 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1590_ok T1707_ok
def T1588 : Node := Node.leaf L1588
theorem T1588_ok : Node.check D_R11111 T1588 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((8025/2048),(535/128))] = true := Node.check_leaf_of _ _ _ L1588_ok
def T1587 : Node := Node.leaf L1587
theorem T1587_ok : Node.check D_R11111 T1587 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((8025/2048),(535/128))] = true := Node.check_leaf_of _ _ _ L1587_ok
def T1586 : Node := Node.split 1 T1587 T1588
theorem T1586_ok : Node.check D_R11111 T1586 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((8025/2048),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1587_ok T1588_ok
def T1585 : Node := Node.leaf L1585
theorem T1585_ok : Node.check D_R11111 T1585 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true := Node.check_leaf_of _ _ _ L1585_ok
def T1584 : Node := Node.leaf L1584
theorem T1584_ok : Node.check D_R11111 T1584 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true := Node.check_leaf_of _ _ _ L1584_ok
def T1583 : Node := Node.split 1 T1584 T1585
theorem T1583_ok : Node.check D_R11111 T1583 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(8025/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1584_ok T1585_ok
def T1582 : Node := Node.split 3 T1583 T1586
theorem T1582_ok : Node.check D_R11111 T1582 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1583_ok T1586_ok
def T1581 : Node := Node.leaf L1581
theorem T1581_ok : Node.check D_R11111 T1581 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1581_ok
def T1580 : Node := Node.split 0 T1581 T1582
theorem T1580_ok : Node.check D_R11111 T1580 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1581_ok T1582_ok
def T1579 : Node := Node.leaf L1579
theorem T1579_ok : Node.check D_R11111 T1579 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1579_ok
def T1578 : Node := Node.split 2 T1579 T1580
theorem T1578_ok : Node.check D_R11111 T1578 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1579_ok T1580_ok
def T1577 : Node := Node.leaf L1577
theorem T1577_ok : Node.check D_R11111 T1577 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((3745/1024),(535/128))] = true := Node.check_leaf_of _ _ _ L1577_ok
def T1576 : Node := Node.split 1 T1577 T1578
theorem T1576_ok : Node.check D_R11111 T1576 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((3745/1024),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1577_ok T1578_ok
def T1575 : Node := Node.leaf L1575
theorem T1575_ok : Node.check D_R11111 T1575 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((6955/2048),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1575_ok
def T1574 : Node := Node.leaf L1574
theorem T1574_ok : Node.check D_R11111 T1574 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1574_ok
def T1573 : Node := Node.leaf L1573
theorem T1573_ok : Node.check D_R11111 T1573 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1573_ok
def T1572 : Node := Node.leaf L1572
theorem T1572_ok : Node.check D_R11111 T1572 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/512),(6955/2048))] = true := Node.check_leaf_of _ _ _ L1572_ok
def T1571 : Node := Node.split 2 T1572 T1573
theorem T1571_ok : Node.check D_R11111 T1571 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1572_ok T1573_ok
def T1570 : Node := Node.split 1 T1571 T1574
theorem T1570_ok : Node.check D_R11111 T1570 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(6955/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1571_ok T1574_ok
def T1569 : Node := Node.split 3 T1570 T1575
theorem T1569_ok : Node.check D_R11111 T1569 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1570_ok T1575_ok
def T1568 : Node := Node.leaf L1568
theorem T1568_ok : Node.check D_R11111 T1568 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1568_ok
def T1567 : Node := Node.split 0 T1568 T1569
theorem T1567_ok : Node.check D_R11111 T1567 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1568_ok T1569_ok
def T1566 : Node := Node.leaf L1566
theorem T1566_ok : Node.check D_R11111 T1566 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1566_ok
def T1565 : Node := Node.split 2 T1566 T1567
theorem T1565_ok : Node.check D_R11111 T1565 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1566_ok T1567_ok
def T1564 : Node := Node.leaf L1564
theorem T1564_ok : Node.check D_R11111 T1564 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((1605/512),(3745/1024))] = true := Node.check_leaf_of _ _ _ L1564_ok
def T1563 : Node := Node.split 1 T1564 T1565
theorem T1563_ok : Node.check D_R11111 T1563 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(3745/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1564_ok T1565_ok
def T1562 : Node := Node.split 3 T1563 T1576
theorem T1562_ok : Node.check D_R11111 T1562 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1563_ok T1576_ok
def T1561 : Node := Node.leaf L1561
theorem T1561_ok : Node.check D_R11111 T1561 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1561_ok
def T1560 : Node := Node.split 0 T1561 T1562
theorem T1560_ok : Node.check D_R11111 T1560 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1561_ok T1562_ok
def T1559 : Node := Node.leaf L1559
theorem T1559_ok : Node.check D_R11111 T1559 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1559_ok
def T1558 : Node := Node.split 2 T1559 T1560
theorem T1558_ok : Node.check D_R11111 T1558 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1559_ok T1560_ok
def T1557 : Node := Node.leaf L1557
theorem T1557_ok : Node.check D_R11111 T1557 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((1605/512),(535/128))] = true := Node.check_leaf_of _ _ _ L1557_ok
def T1556 : Node := Node.split 1 T1557 T1558
theorem T1556_ok : Node.check D_R11111 T1556 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((1605/512),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1557_ok T1558_ok
def T1555 : Node := Node.leaf L1555
theorem T1555_ok : Node.check D_R11111 T1555 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1555_ok
def T1554 : Node := Node.leaf L1554
theorem T1554_ok : Node.check D_R11111 T1554 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1554_ok
def T1553 : Node := Node.leaf L1553
theorem T1553_ok : Node.check D_R11111 T1553 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1553_ok
def T1552 : Node := Node.leaf L1552
theorem T1552_ok : Node.check D_R11111 T1552 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1552_ok
def T1551 : Node := Node.split 2 T1552 T1553
theorem T1551_ok : Node.check D_R11111 T1551 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1552_ok T1553_ok
def T1550 : Node := Node.leaf L1550
theorem T1550_ok : Node.check D_R11111 T1550 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true := Node.check_leaf_of _ _ _ L1550_ok
def T1549 : Node := Node.split 1 T1550 T1551
theorem T1549_ok : Node.check D_R11111 T1549 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((12305/4096),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1550_ok T1551_ok
def T1548 : Node := Node.leaf L1548
theorem T1548_ok : Node.check D_R11111 T1548 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1548_ok
def T1547 : Node := Node.leaf L1547
theorem T1547_ok : Node.check D_R11111 T1547 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1547_ok
def T1546 : Node := Node.split 2 T1547 T1548
theorem T1546_ok : Node.check D_R11111 T1546 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1547_ok T1548_ok
def T1545 : Node := Node.leaf L1545
theorem T1545_ok : Node.check D_R11111 T1545 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true := Node.check_leaf_of _ _ _ L1545_ok
def T1544 : Node := Node.split 1 T1545 T1546
theorem T1544_ok : Node.check D_R11111 T1544 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(12305/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1545_ok T1546_ok
def T1543 : Node := Node.split 3 T1544 T1549
theorem T1543_ok : Node.check D_R11111 T1543 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1544_ok T1549_ok
def T1542 : Node := Node.leaf L1542
theorem T1542_ok : Node.check D_R11111 T1542 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true := Node.check_leaf_of _ _ _ L1542_ok
def T1541 : Node := Node.split 0 T1542 T1543
theorem T1541_ok : Node.check D_R11111 T1541 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1542_ok T1543_ok
def T1540 : Node := Node.split 2 T1541 T1554
theorem T1540_ok : Node.check D_R11111 T1540 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1541_ok T1554_ok
def T1539 : Node := Node.split 1 T1540 T1555
theorem T1539_ok : Node.check D_R11111 T1539 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((5885/2048),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1540_ok T1555_ok
def T1538 : Node := Node.leaf L1538
theorem T1538_ok : Node.check D_R11111 T1538 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1538_ok
def T1537 : Node := Node.leaf L1537
theorem T1537_ok : Node.check D_R11111 T1537 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1537_ok
def T1536 : Node := Node.leaf L1536
theorem T1536_ok : Node.check D_R11111 T1536 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1536_ok
def T1535 : Node := Node.leaf L1535
theorem T1535_ok : Node.check D_R11111 T1535 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1535_ok
def T1534 : Node := Node.split 1 T1535 T1536
theorem T1534_ok : Node.check D_R11111 T1534 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((11235/4096),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1535_ok T1536_ok
def T1533 : Node := Node.leaf L1533
theorem T1533_ok : Node.check D_R11111 T1533 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(11235/4096))] = true := Node.check_leaf_of _ _ _ L1533_ok
def T1532 : Node := Node.split 3 T1533 T1534
theorem T1532_ok : Node.check D_R11111 T1532 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1533_ok T1534_ok
def T1531 : Node := Node.leaf L1531
theorem T1531_ok : Node.check D_R11111 T1531 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true := Node.check_leaf_of _ _ _ L1531_ok
def T1530 : Node := Node.split 0 T1531 T1532
theorem T1530_ok : Node.check D_R11111 T1530 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1531_ok T1532_ok
def T1529 : Node := Node.split 2 T1530 T1537
theorem T1529_ok : Node.check D_R11111 T1529 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1530_ok T1537_ok
def T1528 : Node := Node.split 1 T1529 T1538
theorem T1528_ok : Node.check D_R11111 T1528 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(5885/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1529_ok T1538_ok
def T1527 : Node := Node.split 3 T1528 T1539
theorem T1527_ok : Node.check D_R11111 T1527 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1528_ok T1539_ok
def T1526 : Node := Node.leaf L1526
theorem T1526_ok : Node.check D_R11111 T1526 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1526_ok
def T1525 : Node := Node.split 0 T1526 T1527
theorem T1525_ok : Node.check D_R11111 T1525 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1526_ok T1527_ok
def T1524 : Node := Node.leaf L1524
theorem T1524_ok : Node.check D_R11111 T1524 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1524_ok
def T1523 : Node := Node.split 2 T1524 T1525
theorem T1523_ok : Node.check D_R11111 T1523 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1524_ok T1525_ok
def T1522 : Node := Node.leaf L1522
theorem T1522_ok : Node.check D_R11111 T1522 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((2675/1024),(1605/512))] = true := Node.check_leaf_of _ _ _ L1522_ok
def T1521 : Node := Node.split 1 T1522 T1523
theorem T1521_ok : Node.check D_R11111 T1521 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((2675/1024),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1522_ok T1523_ok
def T1520 : Node := Node.leaf L1520
theorem T1520_ok : Node.check D_R11111 T1520 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((4815/2048),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1520_ok
def T1519 : Node := Node.leaf L1519
theorem T1519_ok : Node.check D_R11111 T1519 [((1605/2048),(535/512)),((2331/2048),(333/256)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1519_ok
def T1518 : Node := Node.leaf L1518
theorem T1518_ok : Node.check D_R11111 T1518 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1518_ok
def T1517 : Node := Node.split 2 T1518 T1519
theorem T1517_ok : Node.check D_R11111 T1517 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1518_ok T1519_ok
def T1516 : Node := Node.leaf L1516
theorem T1516_ok : Node.check D_R11111 T1516 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1516_ok
def T1515 : Node := Node.leaf L1515
theorem T1515_ok : Node.check D_R11111 T1515 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((9095/4096),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1515_ok
def T1514 : Node := Node.leaf L1514
theorem T1514_ok : Node.check D_R11111 T1514 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1514_ok
def T1513 : Node := Node.leaf L1513
theorem T1513_ok : Node.check D_R11111 T1513 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1513_ok
def T1512 : Node := Node.leaf L1512
theorem T1512_ok : Node.check D_R11111 T1512 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1512_ok
def T1511 : Node := Node.split 0 T1512 T1513
theorem T1511_ok : Node.check D_R11111 T1511 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1512_ok T1513_ok
def T1510 : Node := Node.split 2 T1511 T1514
theorem T1510_ok : Node.check D_R11111 T1510 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1511_ok T1514_ok
def T1509 : Node := Node.leaf L1509
theorem T1509_ok : Node.check D_R11111 T1509 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1509_ok
def T1508 : Node := Node.leaf L1508
theorem T1508_ok : Node.check D_R11111 T1508 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1508_ok
def T1507 : Node := Node.leaf L1507
theorem T1507_ok : Node.check D_R11111 T1507 [((3745/4096),(8025/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true := Node.check_leaf_of _ _ _ L1507_ok
def T1506 : Node := Node.split 0 T1507 T1508
theorem T1506_ok : Node.check D_R11111 T1506 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1507_ok T1508_ok
def T1505 : Node := Node.split 2 T1506 T1509
theorem T1505_ok : Node.check D_R11111 T1505 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1506_ok T1509_ok
def T1504 : Node := Node.split 1 T1505 T1510
theorem T1504_ok : Node.check D_R11111 T1504 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(9095/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1505_ok T1510_ok
def T1503 : Node := Node.split 3 T1504 T1515
theorem T1503_ok : Node.check D_R11111 T1503 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1504_ok T1515_ok
def T1502 : Node := Node.leaf L1502
theorem T1502_ok : Node.check D_R11111 T1502 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true := Node.check_leaf_of _ _ _ L1502_ok
def T1501 : Node := Node.split 0 T1502 T1503
theorem T1501_ok : Node.check D_R11111 T1501 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1502_ok T1503_ok
def T1500 : Node := Node.split 2 T1501 T1516
theorem T1500_ok : Node.check D_R11111 T1500 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1501_ok T1516_ok
def T1499 : Node := Node.split 1 T1500 T1517
theorem T1499_ok : Node.check D_R11111 T1499 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(4815/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1500_ok T1517_ok
def T1498 : Node := Node.split 3 T1499 T1520
theorem T1498_ok : Node.check D_R11111 T1498 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1499_ok T1520_ok
def T1497 : Node := Node.leaf L1497
theorem T1497_ok : Node.check D_R11111 T1497 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1497_ok
def T1496 : Node := Node.split 0 T1497 T1498
theorem T1496_ok : Node.check D_R11111 T1496 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1497_ok T1498_ok
def T1495 : Node := Node.leaf L1495
theorem T1495_ok : Node.check D_R11111 T1495 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1495_ok
def T1494 : Node := Node.split 2 T1495 T1496
theorem T1494_ok : Node.check D_R11111 T1494 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1495_ok T1496_ok
def T1493 : Node := Node.leaf L1493
theorem T1493_ok : Node.check D_R11111 T1493 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/256),(2675/1024))] = true := Node.check_leaf_of _ _ _ L1493_ok
def T1492 : Node := Node.split 1 T1493 T1494
theorem T1492_ok : Node.check D_R11111 T1492 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(2675/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1493_ok T1494_ok
def T1491 : Node := Node.split 3 T1492 T1521
theorem T1491_ok : Node.check D_R11111 T1491 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1492_ok T1521_ok
def T1490 : Node := Node.leaf L1490
theorem T1490_ok : Node.check D_R11111 T1490 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1490_ok
def T1489 : Node := Node.split 0 T1490 T1491
theorem T1489_ok : Node.check D_R11111 T1489 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1490_ok T1491_ok
def T1488 : Node := Node.leaf L1488
theorem T1488_ok : Node.check D_R11111 T1488 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1488_ok
def T1487 : Node := Node.split 2 T1488 T1489
theorem T1487_ok : Node.check D_R11111 T1487 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1488_ok T1489_ok
def T1486 : Node := Node.leaf L1486
theorem T1486_ok : Node.check D_R11111 T1486 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((535/256),(1605/512))] = true := Node.check_leaf_of _ _ _ L1486_ok
def T1485 : Node := Node.split 1 T1486 T1487
theorem T1485_ok : Node.check D_R11111 T1485 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((535/256),(1605/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1486_ok T1487_ok
def T1484 : Node := Node.split 3 T1485 T1556
theorem T1484_ok : Node.check D_R11111 T1484 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1485_ok T1556_ok
def T1483 : Node := Node.split 0 T1484 T1589
theorem T1483_ok : Node.check D_R11111 T1483 [((0),(535/256)),((0),(333/256)),((0),(333/256)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1484_ok T1589_ok
def T1482 : Node := Node.split 2 T1483 T1756
theorem T1482_ok : Node.check D_R11111 T1482 [((0),(535/256)),((0),(333/256)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1483_ok T1756_ok
def T1481 : Node := Node.split 1 T1482 T1849
theorem T1481_ok : Node.check D_R11111 T1481 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((535/256),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1482_ok T1849_ok
def T1480 : Node := Node.leaf L1480
theorem T1480_ok : Node.check D_R11111 T1480 [((535/512),(535/256)),((999/512),(333/128)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1480_ok
def T1479 : Node := Node.leaf L1479
theorem T1479_ok : Node.check D_R11111 T1479 [((1605/1024),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1479_ok
def T1478 : Node := Node.leaf L1478
theorem T1478_ok : Node.check D_R11111 T1478 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1478_ok
def T1477 : Node := Node.leaf L1477
theorem T1477_ok : Node.check D_R11111 T1477 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1477_ok
def T1476 : Node := Node.leaf L1476
theorem T1476_ok : Node.check D_R11111 T1476 [((535/512),(1605/1024)),((999/512),(2331/1024)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1476_ok
def T1475 : Node := Node.leaf L1475
theorem T1475_ok : Node.check D_R11111 T1475 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1475_ok
def T1474 : Node := Node.split 2 T1475 T1476
theorem T1474_ok : Node.check D_R11111 T1474 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1475_ok T1476_ok
def T1473 : Node := Node.split 1 T1474 T1477
theorem T1473_ok : Node.check D_R11111 T1473 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1474_ok T1477_ok
def T1472 : Node := Node.split 3 T1473 T1478
theorem T1472_ok : Node.check D_R11111 T1472 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1473_ok T1478_ok
def T1471 : Node := Node.split 0 T1472 T1479
theorem T1471_ok : Node.check D_R11111 T1471 [((535/512),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1472_ok T1479_ok
def T1470 : Node := Node.split 2 T1471 T1480
theorem T1470_ok : Node.check D_R11111 T1470 [((535/512),(535/256)),((999/512),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1471_ok T1480_ok
def T1469 : Node := Node.leaf L1469
theorem T1469_ok : Node.check D_R11111 T1469 [((1605/1024),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1469_ok
def T1468 : Node := Node.leaf L1468
theorem T1468_ok : Node.check D_R11111 T1468 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1468_ok
def T1467 : Node := Node.leaf L1467
theorem T1467_ok : Node.check D_R11111 T1467 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1467_ok
def T1466 : Node := Node.leaf L1466
theorem T1466_ok : Node.check D_R11111 T1466 [((535/512),(1605/1024)),((333/256),(1665/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1466_ok
def T1465 : Node := Node.split 1 T1466 T1467
theorem T1465_ok : Node.check D_R11111 T1465 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1466_ok T1467_ok
def T1464 : Node := Node.split 3 T1465 T1468
theorem T1464_ok : Node.check D_R11111 T1464 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1465_ok T1468_ok
def T1463 : Node := Node.split 0 T1464 T1469
theorem T1463_ok : Node.check D_R11111 T1463 [((535/512),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1464_ok T1469_ok
def T1462 : Node := Node.leaf L1462
theorem T1462_ok : Node.check D_R11111 T1462 [((1605/1024),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1462_ok
def T1461 : Node := Node.leaf L1461
theorem T1461_ok : Node.check D_R11111 T1461 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1461_ok
def T1460 : Node := Node.leaf L1460
theorem T1460_ok : Node.check D_R11111 T1460 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1460_ok
def T1459 : Node := Node.leaf L1459
theorem T1459_ok : Node.check D_R11111 T1459 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1459_ok
def T1458 : Node := Node.split 1 T1459 T1460
theorem T1458_ok : Node.check D_R11111 T1458 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1459_ok T1460_ok
def T1457 : Node := Node.split 3 T1458 T1461
theorem T1457_ok : Node.check D_R11111 T1457 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1458_ok T1461_ok
def T1456 : Node := Node.split 0 T1457 T1462
theorem T1456_ok : Node.check D_R11111 T1456 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1457_ok T1462_ok
def T1455 : Node := Node.split 2 T1456 T1463
theorem T1455_ok : Node.check D_R11111 T1455 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1456_ok T1463_ok
def T1454 : Node := Node.split 1 T1455 T1470
theorem T1454_ok : Node.check D_R11111 T1454 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1455_ok T1470_ok
def T1453 : Node := Node.leaf L1453
theorem T1453_ok : Node.check D_R11111 T1453 [((1605/1024),(535/256)),((999/512),(333/128)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1453_ok
def T1452 : Node := Node.leaf L1452
theorem T1452_ok : Node.check D_R11111 T1452 [((1605/1024),(535/256)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1452_ok
def T1451 : Node := Node.split 3 T1452 T1453
theorem T1451_ok : Node.check D_R11111 T1451 [((1605/1024),(535/256)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1452_ok T1453_ok
def T1450 : Node := Node.leaf L1450
theorem T1450_ok : Node.check D_R11111 T1450 [((535/512),(1605/1024)),((999/512),(333/128)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1450_ok
def T1449 : Node := Node.leaf L1449
theorem T1449_ok : Node.check D_R11111 T1449 [((535/512),(1605/1024)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1449_ok
def T1448 : Node := Node.split 3 T1449 T1450
theorem T1448_ok : Node.check D_R11111 T1448 [((535/512),(1605/1024)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1449_ok T1450_ok
def T1447 : Node := Node.split 0 T1448 T1451
theorem T1447_ok : Node.check D_R11111 T1447 [((535/512),(535/256)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1448_ok T1451_ok
def T1446 : Node := Node.leaf L1446
theorem T1446_ok : Node.check D_R11111 T1446 [((1605/1024),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1446_ok
def T1445 : Node := Node.leaf L1445
theorem T1445_ok : Node.check D_R11111 T1445 [((1605/1024),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1445_ok
def T1444 : Node := Node.split 3 T1445 T1446
theorem T1444_ok : Node.check D_R11111 T1444 [((1605/1024),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1445_ok T1446_ok
def T1443 : Node := Node.leaf L1443
theorem T1443_ok : Node.check D_R11111 T1443 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1443_ok
def T1442 : Node := Node.leaf L1442
theorem T1442_ok : Node.check D_R11111 T1442 [((535/512),(1605/1024)),((999/512),(2331/1024)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1442_ok
def T1441 : Node := Node.leaf L1441
theorem T1441_ok : Node.check D_R11111 T1441 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/256),(1665/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1441_ok
def T1440 : Node := Node.split 2 T1441 T1442
theorem T1440_ok : Node.check D_R11111 T1440 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1441_ok T1442_ok
def T1439 : Node := Node.split 1 T1440 T1443
theorem T1439_ok : Node.check D_R11111 T1439 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1440_ok T1443_ok
def T1438 : Node := Node.leaf L1438
theorem T1438_ok : Node.check D_R11111 T1438 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1438_ok
def T1437 : Node := Node.split 3 T1438 T1439
theorem T1437_ok : Node.check D_R11111 T1437 [((535/512),(1605/1024)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1438_ok T1439_ok
def T1436 : Node := Node.split 0 T1437 T1444
theorem T1436_ok : Node.check D_R11111 T1436 [((535/512),(535/256)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1437_ok T1444_ok
def T1435 : Node := Node.split 2 T1436 T1447
theorem T1435_ok : Node.check D_R11111 T1435 [((535/512),(535/256)),((999/512),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1436_ok T1447_ok
def T1434 : Node := Node.leaf L1434
theorem T1434_ok : Node.check D_R11111 T1434 [((1605/1024),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1434_ok
def T1433 : Node := Node.leaf L1433
theorem T1433_ok : Node.check D_R11111 T1433 [((1605/1024),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1433_ok
def T1432 : Node := Node.split 3 T1433 T1434
theorem T1432_ok : Node.check D_R11111 T1432 [((1605/1024),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1433_ok T1434_ok
def T1431 : Node := Node.leaf L1431
theorem T1431_ok : Node.check D_R11111 T1431 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1431_ok
def T1430 : Node := Node.leaf L1430
theorem T1430_ok : Node.check D_R11111 T1430 [((535/512),(1605/1024)),((333/256),(1665/1024)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1430_ok
def T1429 : Node := Node.split 1 T1430 T1431
theorem T1429_ok : Node.check D_R11111 T1429 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1430_ok T1431_ok
def T1428 : Node := Node.leaf L1428
theorem T1428_ok : Node.check D_R11111 T1428 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1428_ok
def T1427 : Node := Node.split 3 T1428 T1429
theorem T1427_ok : Node.check D_R11111 T1427 [((535/512),(1605/1024)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1428_ok T1429_ok
def T1426 : Node := Node.split 0 T1427 T1432
theorem T1426_ok : Node.check D_R11111 T1426 [((535/512),(535/256)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1427_ok T1432_ok
def T1425 : Node := Node.leaf L1425
theorem T1425_ok : Node.check D_R11111 T1425 [((1605/1024),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1425_ok
def T1424 : Node := Node.leaf L1424
theorem T1424_ok : Node.check D_R11111 T1424 [((1605/1024),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1424_ok
def T1423 : Node := Node.split 3 T1424 T1425
theorem T1423_ok : Node.check D_R11111 T1423 [((1605/1024),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1424_ok T1425_ok
def T1422 : Node := Node.leaf L1422
theorem T1422_ok : Node.check D_R11111 T1422 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1422_ok
def T1421 : Node := Node.leaf L1421
theorem T1421_ok : Node.check D_R11111 T1421 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1421_ok
def T1420 : Node := Node.split 1 T1421 T1422
theorem T1420_ok : Node.check D_R11111 T1420 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1421_ok T1422_ok
def T1419 : Node := Node.leaf L1419
theorem T1419_ok : Node.check D_R11111 T1419 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1419_ok
def T1418 : Node := Node.split 3 T1419 T1420
theorem T1418_ok : Node.check D_R11111 T1418 [((535/512),(1605/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1419_ok T1420_ok
def T1417 : Node := Node.split 0 T1418 T1423
theorem T1417_ok : Node.check D_R11111 T1417 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1418_ok T1423_ok
def T1416 : Node := Node.split 2 T1417 T1426
theorem T1416_ok : Node.check D_R11111 T1416 [((535/512),(535/256)),((333/256),(999/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1417_ok T1426_ok
def T1415 : Node := Node.split 1 T1416 T1435
theorem T1415_ok : Node.check D_R11111 T1415 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1416_ok T1435_ok
def T1414 : Node := Node.split 3 T1415 T1454
theorem T1414_ok : Node.check D_R11111 T1414 [((535/512),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1415_ok T1454_ok
def T1413 : Node := Node.leaf L1413
theorem T1413_ok : Node.check D_R11111 T1413 [((535/1024),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1413_ok
def T1412 : Node := Node.leaf L1412
theorem T1412_ok : Node.check D_R11111 T1412 [((0),(535/1024)),((999/512),(333/128)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1412_ok
def T1411 : Node := Node.split 0 T1412 T1413
theorem T1411_ok : Node.check D_R11111 T1411 [((0),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1412_ok T1413_ok
def T1410 : Node := Node.leaf L1410
theorem T1410_ok : Node.check D_R11111 T1410 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1410_ok
def T1409 : Node := Node.leaf L1409
theorem T1409_ok : Node.check D_R11111 T1409 [((535/1024),(535/512)),((2331/1024),(333/128)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1409_ok
def T1408 : Node := Node.leaf L1408
theorem T1408_ok : Node.check D_R11111 T1408 [((535/1024),(535/512)),((999/512),(2331/1024)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1408_ok
def T1407 : Node := Node.leaf L1407
theorem T1407_ok : Node.check D_R11111 T1407 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1407_ok
def T1406 : Node := Node.split 2 T1407 T1408
theorem T1406_ok : Node.check D_R11111 T1406 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1407_ok T1408_ok
def T1405 : Node := Node.split 1 T1406 T1409
theorem T1405_ok : Node.check D_R11111 T1405 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1406_ok T1409_ok
def T1404 : Node := Node.split 3 T1405 T1410
theorem T1404_ok : Node.check D_R11111 T1404 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1405_ok T1410_ok
def T1403 : Node := Node.leaf L1403
theorem T1403_ok : Node.check D_R11111 T1403 [((0),(535/1024)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1403_ok
def T1402 : Node := Node.split 0 T1403 T1404
theorem T1402_ok : Node.check D_R11111 T1402 [((0),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1403_ok T1404_ok
def T1401 : Node := Node.split 2 T1402 T1411
theorem T1401_ok : Node.check D_R11111 T1401 [((0),(535/512)),((999/512),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1402_ok T1411_ok
def T1400 : Node := Node.leaf L1400
theorem T1400_ok : Node.check D_R11111 T1400 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1400_ok
def T1399 : Node := Node.leaf L1399
theorem T1399_ok : Node.check D_R11111 T1399 [((535/1024),(535/512)),((1665/1024),(999/512)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1399_ok
def T1398 : Node := Node.leaf L1398
theorem T1398_ok : Node.check D_R11111 T1398 [((535/1024),(535/512)),((333/256),(1665/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1398_ok
def T1397 : Node := Node.split 1 T1398 T1399
theorem T1397_ok : Node.check D_R11111 T1397 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1398_ok T1399_ok
def T1396 : Node := Node.split 3 T1397 T1400
theorem T1396_ok : Node.check D_R11111 T1396 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1397_ok T1400_ok
def T1395 : Node := Node.leaf L1395
theorem T1395_ok : Node.check D_R11111 T1395 [((0),(535/1024)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1395_ok
def T1394 : Node := Node.split 0 T1395 T1396
theorem T1394_ok : Node.check D_R11111 T1394 [((0),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1395_ok T1396_ok
def T1393 : Node := Node.leaf L1393
theorem T1393_ok : Node.check D_R11111 T1393 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1393_ok
def T1392 : Node := Node.leaf L1392
theorem T1392_ok : Node.check D_R11111 T1392 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1392_ok
def T1391 : Node := Node.leaf L1391
theorem T1391_ok : Node.check D_R11111 T1391 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1391_ok
def T1390 : Node := Node.split 1 T1391 T1392
theorem T1390_ok : Node.check D_R11111 T1390 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1391_ok T1392_ok
def T1389 : Node := Node.split 3 T1390 T1393
theorem T1389_ok : Node.check D_R11111 T1389 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1390_ok T1393_ok
def T1388 : Node := Node.leaf L1388
theorem T1388_ok : Node.check D_R11111 T1388 [((0),(535/1024)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1388_ok
def T1387 : Node := Node.split 0 T1388 T1389
theorem T1387_ok : Node.check D_R11111 T1387 [((0),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1388_ok T1389_ok
def T1386 : Node := Node.split 2 T1387 T1394
theorem T1386_ok : Node.check D_R11111 T1386 [((0),(535/512)),((333/256),(999/512)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1387_ok T1394_ok
def T1385 : Node := Node.split 1 T1386 T1401
theorem T1385_ok : Node.check D_R11111 T1385 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1386_ok T1401_ok
def T1384 : Node := Node.leaf L1384
theorem T1384_ok : Node.check D_R11111 T1384 [((535/1024),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1384_ok
def T1383 : Node := Node.leaf L1383
theorem T1383_ok : Node.check D_R11111 T1383 [((535/1024),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1383_ok
def T1382 : Node := Node.split 3 T1383 T1384
theorem T1382_ok : Node.check D_R11111 T1382 [((535/1024),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1383_ok T1384_ok
def T1381 : Node := Node.leaf L1381
theorem T1381_ok : Node.check D_R11111 T1381 [((0),(535/1024)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1381_ok
def T1380 : Node := Node.split 0 T1381 T1382
theorem T1380_ok : Node.check D_R11111 T1380 [((0),(535/512)),((999/512),(333/128)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1381_ok T1382_ok
def T1379 : Node := Node.leaf L1379
theorem T1379_ok : Node.check D_R11111 T1379 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1379_ok
def T1378 : Node := Node.leaf L1378
theorem T1378_ok : Node.check D_R11111 T1378 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1378_ok
def T1377 : Node := Node.split 3 T1378 T1379
theorem T1377_ok : Node.check D_R11111 T1377 [((535/1024),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1378_ok T1379_ok
def T1376 : Node := Node.leaf L1376
theorem T1376_ok : Node.check D_R11111 T1376 [((0),(535/1024)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1376_ok
def T1375 : Node := Node.split 0 T1376 T1377
theorem T1375_ok : Node.check D_R11111 T1375 [((0),(535/512)),((999/512),(333/128)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1376_ok T1377_ok
def T1374 : Node := Node.split 2 T1375 T1380
theorem T1374_ok : Node.check D_R11111 T1374 [((0),(535/512)),((999/512),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1375_ok T1380_ok
def T1373 : Node := Node.leaf L1373
theorem T1373_ok : Node.check D_R11111 T1373 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1373_ok
def T1372 : Node := Node.leaf L1372
theorem T1372_ok : Node.check D_R11111 T1372 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1372_ok
def T1371 : Node := Node.split 3 T1372 T1373
theorem T1371_ok : Node.check D_R11111 T1371 [((535/1024),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1372_ok T1373_ok
def T1370 : Node := Node.leaf L1370
theorem T1370_ok : Node.check D_R11111 T1370 [((0),(535/1024)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1370_ok
def T1369 : Node := Node.split 0 T1370 T1371
theorem T1369_ok : Node.check D_R11111 T1369 [((0),(535/512)),((333/256),(999/512)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1370_ok T1371_ok
def T1368 : Node := Node.leaf L1368
theorem T1368_ok : Node.check D_R11111 T1368 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1368_ok
def T1367 : Node := Node.leaf L1367
theorem T1367_ok : Node.check D_R11111 T1367 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1367_ok
def T1366 : Node := Node.split 1 T1367 T1368
theorem T1366_ok : Node.check D_R11111 T1366 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1367_ok T1368_ok
def T1365 : Node := Node.leaf L1365
theorem T1365_ok : Node.check D_R11111 T1365 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1365_ok
def T1364 : Node := Node.split 3 T1365 T1366
theorem T1364_ok : Node.check D_R11111 T1364 [((535/1024),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1365_ok T1366_ok
def T1363 : Node := Node.leaf L1363
theorem T1363_ok : Node.check D_R11111 T1363 [((0),(535/1024)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1363_ok
def T1362 : Node := Node.split 0 T1363 T1364
theorem T1362_ok : Node.check D_R11111 T1362 [((0),(535/512)),((333/256),(999/512)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1363_ok T1364_ok
def T1361 : Node := Node.split 2 T1362 T1369
theorem T1361_ok : Node.check D_R11111 T1361 [((0),(535/512)),((333/256),(999/512)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1362_ok T1369_ok
def T1360 : Node := Node.split 1 T1361 T1374
theorem T1360_ok : Node.check D_R11111 T1360 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1361_ok T1374_ok
def T1359 : Node := Node.split 3 T1360 T1385
theorem T1359_ok : Node.check D_R11111 T1359 [((0),(535/512)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1360_ok T1385_ok
def T1358 : Node := Node.split 0 T1359 T1414
theorem T1358_ok : Node.check D_R11111 T1358 [((0),(535/256)),((333/256),(333/128)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1359_ok T1414_ok
def T1357 : Node := Node.leaf L1357
theorem T1357_ok : Node.check D_R11111 T1357 [((1605/1024),(535/256)),((2331/1024),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1357_ok
def T1356 : Node := Node.leaf L1356
theorem T1356_ok : Node.check D_R11111 T1356 [((1605/1024),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1356_ok
def T1355 : Node := Node.leaf L1355
theorem T1355_ok : Node.check D_R11111 T1355 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1355_ok
def T1354 : Node := Node.split 2 T1355 T1356
theorem T1354_ok : Node.check D_R11111 T1354 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1355_ok T1356_ok
def T1353 : Node := Node.split 1 T1354 T1357
theorem T1353_ok : Node.check D_R11111 T1353 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1354_ok T1357_ok
def T1352 : Node := Node.leaf L1352
theorem T1352_ok : Node.check D_R11111 T1352 [((1605/1024),(535/256)),((2331/1024),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1352_ok
def T1351 : Node := Node.leaf L1351
theorem T1351_ok : Node.check D_R11111 T1351 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1351_ok
def T1350 : Node := Node.leaf L1350
theorem T1350_ok : Node.check D_R11111 T1350 [((3745/2048),(535/256)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1350_ok
def T1349 : Node := Node.leaf L1349
theorem T1349_ok : Node.check D_R11111 T1349 [((3745/2048),(535/256)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1349_ok
def T1348 : Node := Node.leaf L1348
theorem T1348_ok : Node.check D_R11111 T1348 [((8025/4096),(535/256)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1348_ok
def T1347 : Node := Node.leaf L1347
theorem T1347_ok : Node.check D_R11111 T1347 [((8025/4096),(535/256)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1347_ok
def T1346 : Node := Node.leaf L1346
theorem T1346_ok : Node.check D_R11111 T1346 [((8025/4096),(535/256)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1346_ok
def T1345 : Node := Node.split 2 T1346 T1347
theorem T1345_ok : Node.check D_R11111 T1345 [((8025/4096),(535/256)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1346_ok T1347_ok
def T1344 : Node := Node.leaf L1344
theorem T1344_ok : Node.check D_R11111 T1344 [((8025/4096),(535/256)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1344_ok
def T1343 : Node := Node.leaf L1343
theorem T1343_ok : Node.check D_R11111 T1343 [((8025/4096),(535/256)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1343_ok
def T1342 : Node := Node.split 2 T1343 T1344
theorem T1342_ok : Node.check D_R11111 T1342 [((8025/4096),(535/256)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1343_ok T1344_ok
def T1341 : Node := Node.split 1 T1342 T1345
theorem T1341_ok : Node.check D_R11111 T1341 [((8025/4096),(535/256)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1342_ok T1345_ok
def T1340 : Node := Node.split 3 T1341 T1348
theorem T1340_ok : Node.check D_R11111 T1340 [((8025/4096),(535/256)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1341_ok T1348_ok
def T1339 : Node := Node.leaf L1339
theorem T1339_ok : Node.check D_R11111 T1339 [((3745/2048),(8025/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1339_ok
def T1338 : Node := Node.leaf L1338
theorem T1338_ok : Node.check D_R11111 T1338 [((3745/2048),(8025/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1338_ok
def T1337 : Node := Node.leaf L1337
theorem T1337_ok : Node.check D_R11111 T1337 [((3745/2048),(8025/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1337_ok
def T1336 : Node := Node.split 1 T1337 T1338
theorem T1336_ok : Node.check D_R11111 T1336 [((3745/2048),(8025/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1337_ok T1338_ok
def T1335 : Node := Node.split 3 T1336 T1339
theorem T1335_ok : Node.check D_R11111 T1335 [((3745/2048),(8025/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1336_ok T1339_ok
def T1334 : Node := Node.split 0 T1335 T1340
theorem T1334_ok : Node.check D_R11111 T1334 [((3745/2048),(535/256)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1335_ok T1340_ok
def T1333 : Node := Node.split 2 T1334 T1349
theorem T1333_ok : Node.check D_R11111 T1333 [((3745/2048),(535/256)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1334_ok T1349_ok
def T1332 : Node := Node.split 1 T1333 T1350
theorem T1332_ok : Node.check D_R11111 T1332 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1333_ok T1350_ok
def T1331 : Node := Node.split 3 T1332 T1351
theorem T1331_ok : Node.check D_R11111 T1331 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1332_ok T1351_ok
def T1330 : Node := Node.leaf L1330
theorem T1330_ok : Node.check D_R11111 T1330 [((1605/1024),(3745/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1330_ok
def T1329 : Node := Node.split 0 T1330 T1331
theorem T1329_ok : Node.check D_R11111 T1329 [((1605/1024),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1330_ok T1331_ok
def T1328 : Node := Node.leaf L1328
theorem T1328_ok : Node.check D_R11111 T1328 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1328_ok
def T1327 : Node := Node.split 2 T1328 T1329
theorem T1327_ok : Node.check D_R11111 T1327 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1328_ok T1329_ok
def T1326 : Node := Node.split 1 T1327 T1352
theorem T1326_ok : Node.check D_R11111 T1326 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1327_ok T1352_ok
def T1325 : Node := Node.split 3 T1326 T1353
theorem T1325_ok : Node.check D_R11111 T1325 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1326_ok T1353_ok
def T1324 : Node := Node.leaf L1324
theorem T1324_ok : Node.check D_R11111 T1324 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1324_ok
def T1323 : Node := Node.leaf L1323
theorem T1323_ok : Node.check D_R11111 T1323 [((2675/2048),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1323_ok
def T1322 : Node := Node.leaf L1322
theorem T1322_ok : Node.check D_R11111 T1322 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1322_ok
def T1321 : Node := Node.leaf L1321
theorem T1321_ok : Node.check D_R11111 T1321 [((535/512),(2675/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1321_ok
def T1320 : Node := Node.leaf L1320
theorem T1320_ok : Node.check D_R11111 T1320 [((4815/4096),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1320_ok
def T1319 : Node := Node.leaf L1319
theorem T1319_ok : Node.check D_R11111 T1319 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1319_ok
def T1318 : Node := Node.leaf L1318
theorem T1318_ok : Node.check D_R11111 T1318 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1318_ok
def T1317 : Node := Node.split 2 T1318 T1319
theorem T1317_ok : Node.check D_R11111 T1317 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1318_ok T1319_ok
def T1316 : Node := Node.leaf L1316
theorem T1316_ok : Node.check D_R11111 T1316 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1316_ok
def T1315 : Node := Node.leaf L1315
theorem T1315_ok : Node.check D_R11111 T1315 [((535/512),(9095/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1315_ok
def T1314 : Node := Node.split 0 T1315 T1316
theorem T1314_ok : Node.check D_R11111 T1314 [((535/512),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1315_ok T1316_ok
def T1313 : Node := Node.leaf L1313
theorem T1313_ok : Node.check D_R11111 T1313 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1313_ok
def T1312 : Node := Node.split 2 T1313 T1314
theorem T1312_ok : Node.check D_R11111 T1312 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1313_ok T1314_ok
def T1311 : Node := Node.split 1 T1312 T1317
theorem T1311_ok : Node.check D_R11111 T1311 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1312_ok T1317_ok
def T1310 : Node := Node.leaf L1310
theorem T1310_ok : Node.check D_R11111 T1310 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L1310_ok
def T1309 : Node := Node.leaf L1309
theorem T1309_ok : Node.check D_R11111 T1309 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L1309_ok
def T1308 : Node := Node.split 1 T1309 T1310
theorem T1308_ok : Node.check D_R11111 T1308 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1309_ok T1310_ok
def T1307 : Node := Node.split 3 T1308 T1311
theorem T1307_ok : Node.check D_R11111 T1307 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1308_ok T1311_ok
def T1306 : Node := Node.split 0 T1307 T1320
theorem T1306_ok : Node.check D_R11111 T1306 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1307_ok T1320_ok
def T1305 : Node := Node.split 2 T1306 T1321
theorem T1305_ok : Node.check D_R11111 T1305 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1306_ok T1321_ok
def T1304 : Node := Node.split 1 T1305 T1322
theorem T1304_ok : Node.check D_R11111 T1304 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1305_ok T1322_ok
def T1303 : Node := Node.leaf L1303
theorem T1303_ok : Node.check D_R11111 T1303 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L1303_ok
def T1302 : Node := Node.split 3 T1303 T1304
theorem T1302_ok : Node.check D_R11111 T1302 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1303_ok T1304_ok
def T1301 : Node := Node.split 0 T1302 T1323
theorem T1301_ok : Node.check D_R11111 T1301 [((535/512),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1302_ok T1323_ok
def T1300 : Node := Node.leaf L1300
theorem T1300_ok : Node.check D_R11111 T1300 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1300_ok
def T1299 : Node := Node.split 2 T1300 T1301
theorem T1299_ok : Node.check D_R11111 T1299 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1300_ok T1301_ok
def T1298 : Node := Node.split 1 T1299 T1324
theorem T1298_ok : Node.check D_R11111 T1298 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1299_ok T1324_ok
def T1297 : Node := Node.leaf L1297
theorem T1297_ok : Node.check D_R11111 T1297 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1297_ok
def T1296 : Node := Node.leaf L1296
theorem T1296_ok : Node.check D_R11111 T1296 [((2675/2048),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1296_ok
def T1295 : Node := Node.leaf L1295
theorem T1295_ok : Node.check D_R11111 T1295 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1295_ok
def T1294 : Node := Node.leaf L1294
theorem T1294_ok : Node.check D_R11111 T1294 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1294_ok
def T1293 : Node := Node.leaf L1293
theorem T1293_ok : Node.check D_R11111 T1293 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1293_ok
def T1292 : Node := Node.split 2 T1293 T1294
theorem T1292_ok : Node.check D_R11111 T1292 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1293_ok T1294_ok
def T1291 : Node := Node.leaf L1291
theorem T1291_ok : Node.check D_R11111 T1291 [((535/512),(2675/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1291_ok
def T1290 : Node := Node.leaf L1290
theorem T1290_ok : Node.check D_R11111 T1290 [((4815/4096),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1290_ok
def T1289 : Node := Node.leaf L1289
theorem T1289_ok : Node.check D_R11111 T1289 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1289_ok
def T1288 : Node := Node.leaf L1288
theorem T1288_ok : Node.check D_R11111 T1288 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1288_ok
def T1287 : Node := Node.leaf L1287
theorem T1287_ok : Node.check D_R11111 T1287 [((9095/8192),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1287_ok
def T1286 : Node := Node.leaf L1286
theorem T1286_ok : Node.check D_R11111 T1286 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1286_ok
def T1285 : Node := Node.leaf L1285
theorem T1285_ok : Node.check D_R11111 T1285 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1285_ok
def T1284 : Node := Node.split 3 T1285 T1286
theorem T1284_ok : Node.check D_R11111 T1284 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1285_ok T1286_ok
def T1283 : Node := Node.split 0 T1284 T1287
theorem T1283_ok : Node.check D_R11111 T1283 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1284_ok T1287_ok
def T1282 : Node := Node.split 2 T1283 T1288
theorem T1282_ok : Node.check D_R11111 T1282 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1283_ok T1288_ok
def T1281 : Node := Node.leaf L1281
theorem T1281_ok : Node.check D_R11111 T1281 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1281_ok
def T1280 : Node := Node.leaf L1280
theorem T1280_ok : Node.check D_R11111 T1280 [((535/512),(9095/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1280_ok
def T1279 : Node := Node.leaf L1279
theorem T1279_ok : Node.check D_R11111 T1279 [((535/512),(9095/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1279_ok
def T1278 : Node := Node.split 3 T1279 T1280
theorem T1278_ok : Node.check D_R11111 T1278 [((535/512),(9095/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1279_ok T1280_ok
def T1277 : Node := Node.split 0 T1278 T1281
theorem T1277_ok : Node.check D_R11111 T1277 [((535/512),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1278_ok T1281_ok
def T1276 : Node := Node.leaf L1276
theorem T1276_ok : Node.check D_R11111 T1276 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1276_ok
def T1275 : Node := Node.leaf L1275
theorem T1275_ok : Node.check D_R11111 T1275 [((535/512),(9095/8192)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1275_ok
def T1274 : Node := Node.split 0 T1275 T1276
theorem T1274_ok : Node.check D_R11111 T1274 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1275_ok T1276_ok
def T1273 : Node := Node.split 2 T1274 T1277
theorem T1273_ok : Node.check D_R11111 T1273 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1274_ok T1277_ok
def T1272 : Node := Node.split 1 T1273 T1282
theorem T1272_ok : Node.check D_R11111 T1272 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1273_ok T1282_ok
def T1271 : Node := Node.split 3 T1272 T1289
theorem T1271_ok : Node.check D_R11111 T1271 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1272_ok T1289_ok
def T1270 : Node := Node.split 0 T1271 T1290
theorem T1270_ok : Node.check D_R11111 T1270 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1271_ok T1290_ok
def T1269 : Node := Node.split 2 T1270 T1291
theorem T1269_ok : Node.check D_R11111 T1269 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1270_ok T1291_ok
def T1268 : Node := Node.split 1 T1269 T1292
theorem T1268_ok : Node.check D_R11111 T1268 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1269_ok T1292_ok
def T1267 : Node := Node.split 3 T1268 T1295
theorem T1267_ok : Node.check D_R11111 T1267 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1268_ok T1295_ok
def T1266 : Node := Node.split 0 T1267 T1296
theorem T1266_ok : Node.check D_R11111 T1266 [((535/512),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1267_ok T1296_ok
def T1265 : Node := Node.leaf L1265
theorem T1265_ok : Node.check D_R11111 T1265 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1265_ok
def T1264 : Node := Node.split 2 T1265 T1266
theorem T1264_ok : Node.check D_R11111 T1264 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1265_ok T1266_ok
def T1263 : Node := Node.split 1 T1264 T1297
theorem T1263_ok : Node.check D_R11111 T1263 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1264_ok T1297_ok
def T1262 : Node := Node.split 3 T1263 T1298
theorem T1262_ok : Node.check D_R11111 T1262 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1263_ok T1298_ok
def T1261 : Node := Node.split 0 T1262 T1325
theorem T1261_ok : Node.check D_R11111 T1261 [((535/512),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1262_ok T1325_ok
def T1260 : Node := Node.leaf L1260
theorem T1260_ok : Node.check D_R11111 T1260 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1260_ok
def T1259 : Node := Node.split 2 T1260 T1261
theorem T1259_ok : Node.check D_R11111 T1259 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1260_ok T1261_ok
def T1258 : Node := Node.leaf L1258
theorem T1258_ok : Node.check D_R11111 T1258 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1258_ok
def T1257 : Node := Node.leaf L1257
theorem T1257_ok : Node.check D_R11111 T1257 [((1605/1024),(535/256)),((333/256),(1665/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1257_ok
def T1256 : Node := Node.split 1 T1257 T1258
theorem T1256_ok : Node.check D_R11111 T1256 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1257_ok T1258_ok
def T1255 : Node := Node.leaf L1255
theorem T1255_ok : Node.check D_R11111 T1255 [((3745/2048),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1255_ok
def T1254 : Node := Node.leaf L1254
theorem T1254_ok : Node.check D_R11111 T1254 [((3745/2048),(535/256)),((3663/2048),(999/512)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1254_ok
def T1253 : Node := Node.leaf L1253
theorem T1253_ok : Node.check D_R11111 T1253 [((3745/2048),(535/256)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1253_ok
def T1252 : Node := Node.split 2 T1253 T1254
theorem T1252_ok : Node.check D_R11111 T1252 [((3745/2048),(535/256)),((3663/2048),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1253_ok T1254_ok
def T1251 : Node := Node.leaf L1251
theorem T1251_ok : Node.check D_R11111 T1251 [((3745/2048),(535/256)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1251_ok
def T1250 : Node := Node.split 1 T1251 T1252
theorem T1250_ok : Node.check D_R11111 T1250 [((3745/2048),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1251_ok T1252_ok
def T1249 : Node := Node.split 3 T1250 T1255
theorem T1249_ok : Node.check D_R11111 T1249 [((3745/2048),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1250_ok T1255_ok
def T1248 : Node := Node.leaf L1248
theorem T1248_ok : Node.check D_R11111 T1248 [((1605/1024),(3745/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1248_ok
def T1247 : Node := Node.split 0 T1248 T1249
theorem T1247_ok : Node.check D_R11111 T1247 [((1605/1024),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1248_ok T1249_ok
def T1246 : Node := Node.leaf L1246
theorem T1246_ok : Node.check D_R11111 T1246 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1246_ok
def T1245 : Node := Node.split 2 T1246 T1247
theorem T1245_ok : Node.check D_R11111 T1245 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1246_ok T1247_ok
def T1244 : Node := Node.leaf L1244
theorem T1244_ok : Node.check D_R11111 T1244 [((1605/1024),(535/256)),((333/256),(1665/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1244_ok
def T1243 : Node := Node.split 1 T1244 T1245
theorem T1243_ok : Node.check D_R11111 T1243 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1244_ok T1245_ok
def T1242 : Node := Node.split 3 T1243 T1256
theorem T1242_ok : Node.check D_R11111 T1242 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1243_ok T1256_ok
def T1241 : Node := Node.leaf L1241
theorem T1241_ok : Node.check D_R11111 T1241 [((2675/2048),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1241_ok
def T1240 : Node := Node.leaf L1240
theorem T1240_ok : Node.check D_R11111 T1240 [((535/512),(2675/2048)),((3663/2048),(999/512)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1240_ok
def T1239 : Node := Node.leaf L1239
theorem T1239_ok : Node.check D_R11111 T1239 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1239_ok
def T1238 : Node := Node.split 2 T1239 T1240
theorem T1238_ok : Node.check D_R11111 T1238 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1239_ok T1240_ok
def T1237 : Node := Node.leaf L1237
theorem T1237_ok : Node.check D_R11111 T1237 [((535/512),(2675/2048)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1237_ok
def T1236 : Node := Node.split 1 T1237 T1238
theorem T1236_ok : Node.check D_R11111 T1236 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1237_ok T1238_ok
def T1235 : Node := Node.leaf L1235
theorem T1235_ok : Node.check D_R11111 T1235 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L1235_ok
def T1234 : Node := Node.split 3 T1235 T1236
theorem T1234_ok : Node.check D_R11111 T1234 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1235_ok T1236_ok
def T1233 : Node := Node.split 0 T1234 T1241
theorem T1233_ok : Node.check D_R11111 T1233 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1234_ok T1241_ok
def T1232 : Node := Node.leaf L1232
theorem T1232_ok : Node.check D_R11111 T1232 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1232_ok
def T1231 : Node := Node.split 2 T1232 T1233
theorem T1231_ok : Node.check D_R11111 T1231 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1232_ok T1233_ok
def T1230 : Node := Node.leaf L1230
theorem T1230_ok : Node.check D_R11111 T1230 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1230_ok
def T1229 : Node := Node.split 1 T1230 T1231
theorem T1229_ok : Node.check D_R11111 T1229 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1230_ok T1231_ok
def T1228 : Node := Node.leaf L1228
theorem T1228_ok : Node.check D_R11111 T1228 [((2675/2048),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1228_ok
def T1227 : Node := Node.leaf L1227
theorem T1227_ok : Node.check D_R11111 T1227 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1227_ok
def T1226 : Node := Node.leaf L1226
theorem T1226_ok : Node.check D_R11111 T1226 [((535/512),(2675/2048)),((3663/2048),(999/512)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1226_ok
def T1225 : Node := Node.leaf L1225
theorem T1225_ok : Node.check D_R11111 T1225 [((4815/4096),(2675/2048)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1225_ok
def T1224 : Node := Node.leaf L1224
theorem T1224_ok : Node.check D_R11111 T1224 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1224_ok
def T1223 : Node := Node.leaf L1223
theorem T1223_ok : Node.check D_R11111 T1223 [((9095/8192),(4815/4096)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1223_ok
def T1222 : Node := Node.leaf L1222
theorem T1222_ok : Node.check D_R11111 T1222 [((9095/8192),(4815/4096)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1222_ok
def T1221 : Node := Node.split 3 T1222 T1223
theorem T1221_ok : Node.check D_R11111 T1221 [((9095/8192),(4815/4096)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1222_ok T1223_ok
def T1220 : Node := Node.leaf L1220
theorem T1220_ok : Node.check D_R11111 T1220 [((535/512),(9095/8192)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1220_ok
def T1219 : Node := Node.leaf L1219
theorem T1219_ok : Node.check D_R11111 T1219 [((535/512),(9095/8192)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1219_ok
def T1218 : Node := Node.split 3 T1219 T1220
theorem T1218_ok : Node.check D_R11111 T1218 [((535/512),(9095/8192)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1219_ok T1220_ok
def T1217 : Node := Node.split 0 T1218 T1221
theorem T1217_ok : Node.check D_R11111 T1217 [((535/512),(4815/4096)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1218_ok T1221_ok
def T1216 : Node := Node.leaf L1216
theorem T1216_ok : Node.check D_R11111 T1216 [((535/512),(4815/4096)),((7659/4096),(999/512)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1216_ok
def T1215 : Node := Node.split 2 T1216 T1217
theorem T1215_ok : Node.check D_R11111 T1215 [((535/512),(4815/4096)),((7659/4096),(999/512)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1216_ok T1217_ok
def T1214 : Node := Node.leaf L1214
theorem T1214_ok : Node.check D_R11111 T1214 [((535/512),(4815/4096)),((3663/2048),(7659/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1214_ok
def T1213 : Node := Node.split 1 T1214 T1215
theorem T1213_ok : Node.check D_R11111 T1213 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1214_ok T1215_ok
def T1212 : Node := Node.split 3 T1213 T1224
theorem T1212_ok : Node.check D_R11111 T1212 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1213_ok T1224_ok
def T1211 : Node := Node.split 0 T1212 T1225
theorem T1211_ok : Node.check D_R11111 T1211 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1212_ok T1225_ok
def T1210 : Node := Node.split 2 T1211 T1226
theorem T1210_ok : Node.check D_R11111 T1210 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1211_ok T1226_ok
def T1209 : Node := Node.leaf L1209
theorem T1209_ok : Node.check D_R11111 T1209 [((535/512),(2675/2048)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1209_ok
def T1208 : Node := Node.split 1 T1209 T1210
theorem T1208_ok : Node.check D_R11111 T1208 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1209_ok T1210_ok
def T1207 : Node := Node.split 3 T1208 T1227
theorem T1207_ok : Node.check D_R11111 T1207 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1208_ok T1227_ok
def T1206 : Node := Node.split 0 T1207 T1228
theorem T1206_ok : Node.check D_R11111 T1206 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1207_ok T1228_ok
def T1205 : Node := Node.leaf L1205
theorem T1205_ok : Node.check D_R11111 T1205 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1205_ok
def T1204 : Node := Node.split 2 T1205 T1206
theorem T1204_ok : Node.check D_R11111 T1204 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1205_ok T1206_ok
def T1203 : Node := Node.leaf L1203
theorem T1203_ok : Node.check D_R11111 T1203 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1203_ok
def T1202 : Node := Node.split 1 T1203 T1204
theorem T1202_ok : Node.check D_R11111 T1202 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1203_ok T1204_ok
def T1201 : Node := Node.split 3 T1202 T1229
theorem T1201_ok : Node.check D_R11111 T1201 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1202_ok T1229_ok
def T1200 : Node := Node.split 0 T1201 T1242
theorem T1200_ok : Node.check D_R11111 T1200 [((535/512),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1201_ok T1242_ok
def T1199 : Node := Node.leaf L1199
theorem T1199_ok : Node.check D_R11111 T1199 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1199_ok
def T1198 : Node := Node.split 2 T1199 T1200
theorem T1198_ok : Node.check D_R11111 T1198 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1199_ok T1200_ok
def T1197 : Node := Node.split 1 T1198 T1259
theorem T1197_ok : Node.check D_R11111 T1197 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1198_ok T1259_ok
def T1196 : Node := Node.leaf L1196
theorem T1196_ok : Node.check D_R11111 T1196 [((1605/1024),(535/256)),((2331/1024),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1196_ok
def T1195 : Node := Node.leaf L1195
theorem T1195_ok : Node.check D_R11111 T1195 [((3745/2048),(535/256)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1195_ok
def T1194 : Node := Node.leaf L1194
theorem T1194_ok : Node.check D_R11111 T1194 [((3745/2048),(535/256)),((999/512),(4329/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1194_ok
def T1193 : Node := Node.leaf L1193
theorem T1193_ok : Node.check D_R11111 T1193 [((3745/2048),(535/256)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1193_ok
def T1192 : Node := Node.split 2 T1193 T1194
theorem T1192_ok : Node.check D_R11111 T1192 [((3745/2048),(535/256)),((999/512),(4329/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1193_ok T1194_ok
def T1191 : Node := Node.split 1 T1192 T1195
theorem T1191_ok : Node.check D_R11111 T1191 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1192_ok T1195_ok
def T1190 : Node := Node.leaf L1190
theorem T1190_ok : Node.check D_R11111 T1190 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L1190_ok
def T1189 : Node := Node.split 3 T1190 T1191
theorem T1189_ok : Node.check D_R11111 T1189 [((3745/2048),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1190_ok T1191_ok
def T1188 : Node := Node.leaf L1188
theorem T1188_ok : Node.check D_R11111 T1188 [((1605/1024),(3745/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1188_ok
def T1187 : Node := Node.split 0 T1188 T1189
theorem T1187_ok : Node.check D_R11111 T1187 [((1605/1024),(535/256)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1188_ok T1189_ok
def T1186 : Node := Node.leaf L1186
theorem T1186_ok : Node.check D_R11111 T1186 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1186_ok
def T1185 : Node := Node.split 2 T1186 T1187
theorem T1185_ok : Node.check D_R11111 T1185 [((1605/1024),(535/256)),((999/512),(2331/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1186_ok T1187_ok
def T1184 : Node := Node.split 1 T1185 T1196
theorem T1184_ok : Node.check D_R11111 T1184 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1185_ok T1196_ok
def T1183 : Node := Node.leaf L1183
theorem T1183_ok : Node.check D_R11111 T1183 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1183_ok
def T1182 : Node := Node.split 3 T1183 T1184
theorem T1182_ok : Node.check D_R11111 T1182 [((1605/1024),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1183_ok T1184_ok
def T1181 : Node := Node.leaf L1181
theorem T1181_ok : Node.check D_R11111 T1181 [((535/512),(1605/1024)),((2331/1024),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1181_ok
def T1180 : Node := Node.leaf L1180
theorem T1180_ok : Node.check D_R11111 T1180 [((2675/2048),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1180_ok
def T1179 : Node := Node.leaf L1179
theorem T1179_ok : Node.check D_R11111 T1179 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1179_ok
def T1178 : Node := Node.leaf L1178
theorem T1178_ok : Node.check D_R11111 T1178 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1178_ok
def T1177 : Node := Node.split 2 T1178 T1179
theorem T1177_ok : Node.check D_R11111 T1177 [((535/512),(2675/2048)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1178_ok T1179_ok
def T1176 : Node := Node.leaf L1176
theorem T1176_ok : Node.check D_R11111 T1176 [((535/512),(2675/2048)),((999/512),(4329/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1176_ok
def T1175 : Node := Node.leaf L1175
theorem T1175_ok : Node.check D_R11111 T1175 [((4815/4096),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1175_ok
def T1174 : Node := Node.leaf L1174
theorem T1174_ok : Node.check D_R11111 T1174 [((9095/8192),(4815/4096)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1174_ok
def T1173 : Node := Node.leaf L1173
theorem T1173_ok : Node.check D_R11111 T1173 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L1173_ok
def T1172 : Node := Node.leaf L1172
theorem T1172_ok : Node.check D_R11111 T1172 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L1172_ok
def T1171 : Node := Node.split 3 T1172 T1173
theorem T1171_ok : Node.check D_R11111 T1171 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1172_ok T1173_ok
def T1170 : Node := Node.split 0 T1171 T1174
theorem T1170_ok : Node.check D_R11111 T1170 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1171_ok T1174_ok
def T1169 : Node := Node.leaf L1169
theorem T1169_ok : Node.check D_R11111 T1169 [((9095/8192),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1169_ok
def T1168 : Node := Node.leaf L1168
theorem T1168_ok : Node.check D_R11111 T1168 [((535/512),(9095/8192)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1168_ok
def T1167 : Node := Node.split 0 T1168 T1169
theorem T1167_ok : Node.check D_R11111 T1167 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1168_ok T1169_ok
def T1166 : Node := Node.split 2 T1167 T1170
theorem T1166_ok : Node.check D_R11111 T1166 [((535/512),(4815/4096)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1167_ok T1170_ok
def T1165 : Node := Node.leaf L1165
theorem T1165_ok : Node.check D_R11111 T1165 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L1165_ok
def T1164 : Node := Node.leaf L1164
theorem T1164_ok : Node.check D_R11111 T1164 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L1164_ok
def T1163 : Node := Node.split 3 T1164 T1165
theorem T1163_ok : Node.check D_R11111 T1163 [((9095/8192),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1164_ok T1165_ok
def T1162 : Node := Node.leaf L1162
theorem T1162_ok : Node.check D_R11111 T1162 [((535/512),(9095/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1162_ok
def T1161 : Node := Node.split 0 T1162 T1163
theorem T1161_ok : Node.check D_R11111 T1161 [((535/512),(4815/4096)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1162_ok T1163_ok
def T1160 : Node := Node.leaf L1160
theorem T1160_ok : Node.check D_R11111 T1160 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1160_ok
def T1159 : Node := Node.split 2 T1160 T1161
theorem T1159_ok : Node.check D_R11111 T1159 [((535/512),(4815/4096)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1160_ok T1161_ok
def T1158 : Node := Node.split 1 T1159 T1166
theorem T1158_ok : Node.check D_R11111 T1158 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1159_ok T1166_ok
def T1157 : Node := Node.leaf L1157
theorem T1157_ok : Node.check D_R11111 T1157 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L1157_ok
def T1156 : Node := Node.split 3 T1157 T1158
theorem T1156_ok : Node.check D_R11111 T1156 [((535/512),(4815/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1157_ok T1158_ok
def T1155 : Node := Node.split 0 T1156 T1175
theorem T1155_ok : Node.check D_R11111 T1155 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1156_ok T1175_ok
def T1154 : Node := Node.split 2 T1155 T1176
theorem T1154_ok : Node.check D_R11111 T1154 [((535/512),(2675/2048)),((999/512),(4329/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1155_ok T1176_ok
def T1153 : Node := Node.split 1 T1154 T1177
theorem T1153_ok : Node.check D_R11111 T1153 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1154_ok T1177_ok
def T1152 : Node := Node.leaf L1152
theorem T1152_ok : Node.check D_R11111 T1152 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L1152_ok
def T1151 : Node := Node.split 3 T1152 T1153
theorem T1151_ok : Node.check D_R11111 T1151 [((535/512),(2675/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1152_ok T1153_ok
def T1150 : Node := Node.split 0 T1151 T1180
theorem T1150_ok : Node.check D_R11111 T1150 [((535/512),(1605/1024)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1151_ok T1180_ok
def T1149 : Node := Node.leaf L1149
theorem T1149_ok : Node.check D_R11111 T1149 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1149_ok
def T1148 : Node := Node.split 2 T1149 T1150
theorem T1148_ok : Node.check D_R11111 T1148 [((535/512),(1605/1024)),((999/512),(2331/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1149_ok T1150_ok
def T1147 : Node := Node.split 1 T1148 T1181
theorem T1147_ok : Node.check D_R11111 T1147 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1148_ok T1181_ok
def T1146 : Node := Node.leaf L1146
theorem T1146_ok : Node.check D_R11111 T1146 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1146_ok
def T1145 : Node := Node.split 3 T1146 T1147
theorem T1145_ok : Node.check D_R11111 T1145 [((535/512),(1605/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1146_ok T1147_ok
def T1144 : Node := Node.split 0 T1145 T1182
theorem T1144_ok : Node.check D_R11111 T1144 [((535/512),(535/256)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1145_ok T1182_ok
def T1143 : Node := Node.leaf L1143
theorem T1143_ok : Node.check D_R11111 T1143 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1143_ok
def T1142 : Node := Node.split 2 T1143 T1144
theorem T1142_ok : Node.check D_R11111 T1142 [((535/512),(535/256)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1143_ok T1144_ok
def T1141 : Node := Node.leaf L1141
theorem T1141_ok : Node.check D_R11111 T1141 [((3745/2048),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1141_ok
def T1140 : Node := Node.leaf L1140
theorem T1140_ok : Node.check D_R11111 T1140 [((1605/1024),(3745/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1140_ok
def T1139 : Node := Node.split 0 T1140 T1141
theorem T1139_ok : Node.check D_R11111 T1139 [((1605/1024),(535/256)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1140_ok T1141_ok
def T1138 : Node := Node.leaf L1138
theorem T1138_ok : Node.check D_R11111 T1138 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1138_ok
def T1137 : Node := Node.split 2 T1138 T1139
theorem T1137_ok : Node.check D_R11111 T1137 [((1605/1024),(535/256)),((1665/1024),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1138_ok T1139_ok
def T1136 : Node := Node.leaf L1136
theorem T1136_ok : Node.check D_R11111 T1136 [((1605/1024),(535/256)),((333/256),(1665/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1136_ok
def T1135 : Node := Node.split 1 T1136 T1137
theorem T1135_ok : Node.check D_R11111 T1135 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1136_ok T1137_ok
def T1134 : Node := Node.leaf L1134
theorem T1134_ok : Node.check D_R11111 T1134 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1134_ok
def T1133 : Node := Node.split 3 T1134 T1135
theorem T1133_ok : Node.check D_R11111 T1133 [((1605/1024),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1134_ok T1135_ok
def T1132 : Node := Node.leaf L1132
theorem T1132_ok : Node.check D_R11111 T1132 [((2675/2048),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1132_ok
def T1131 : Node := Node.leaf L1131
theorem T1131_ok : Node.check D_R11111 T1131 [((535/512),(2675/2048)),((3663/2048),(999/512)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1131_ok
def T1130 : Node := Node.leaf L1130
theorem T1130_ok : Node.check D_R11111 T1130 [((4815/4096),(2675/2048)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1130_ok
def T1129 : Node := Node.leaf L1129
theorem T1129_ok : Node.check D_R11111 T1129 [((535/512),(4815/4096)),((7659/4096),(999/512)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1129_ok
def T1128 : Node := Node.leaf L1128
theorem T1128_ok : Node.check D_R11111 T1128 [((535/512),(4815/4096)),((3663/2048),(7659/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L1128_ok
def T1127 : Node := Node.split 1 T1128 T1129
theorem T1127_ok : Node.check D_R11111 T1127 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1128_ok T1129_ok
def T1126 : Node := Node.leaf L1126
theorem T1126_ok : Node.check D_R11111 T1126 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L1126_ok
def T1125 : Node := Node.split 3 T1126 T1127
theorem T1125_ok : Node.check D_R11111 T1125 [((535/512),(4815/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1126_ok T1127_ok
def T1124 : Node := Node.split 0 T1125 T1130
theorem T1124_ok : Node.check D_R11111 T1124 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1125_ok T1130_ok
def T1123 : Node := Node.split 2 T1124 T1131
theorem T1123_ok : Node.check D_R11111 T1123 [((535/512),(2675/2048)),((3663/2048),(999/512)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1124_ok T1131_ok
def T1122 : Node := Node.leaf L1122
theorem T1122_ok : Node.check D_R11111 T1122 [((535/512),(2675/2048)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L1122_ok
def T1121 : Node := Node.split 1 T1122 T1123
theorem T1121_ok : Node.check D_R11111 T1121 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1122_ok T1123_ok
def T1120 : Node := Node.leaf L1120
theorem T1120_ok : Node.check D_R11111 T1120 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L1120_ok
def T1119 : Node := Node.split 3 T1120 T1121
theorem T1119_ok : Node.check D_R11111 T1119 [((535/512),(2675/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1120_ok T1121_ok
def T1118 : Node := Node.split 0 T1119 T1132
theorem T1118_ok : Node.check D_R11111 T1118 [((535/512),(1605/1024)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1119_ok T1132_ok
def T1117 : Node := Node.leaf L1117
theorem T1117_ok : Node.check D_R11111 T1117 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1117_ok
def T1116 : Node := Node.split 2 T1117 T1118
theorem T1116_ok : Node.check D_R11111 T1116 [((535/512),(1605/1024)),((1665/1024),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1117_ok T1118_ok
def T1115 : Node := Node.leaf L1115
theorem T1115_ok : Node.check D_R11111 T1115 [((535/512),(1605/1024)),((333/256),(1665/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L1115_ok
def T1114 : Node := Node.split 1 T1115 T1116
theorem T1114_ok : Node.check D_R11111 T1114 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1115_ok T1116_ok
def T1113 : Node := Node.leaf L1113
theorem T1113_ok : Node.check D_R11111 T1113 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L1113_ok
def T1112 : Node := Node.split 3 T1113 T1114
theorem T1112_ok : Node.check D_R11111 T1112 [((535/512),(1605/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1113_ok T1114_ok
def T1111 : Node := Node.split 0 T1112 T1133
theorem T1111_ok : Node.check D_R11111 T1111 [((535/512),(535/256)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1112_ok T1133_ok
def T1110 : Node := Node.leaf L1110
theorem T1110_ok : Node.check D_R11111 T1110 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L1110_ok
def T1109 : Node := Node.split 2 T1110 T1111
theorem T1109_ok : Node.check D_R11111 T1109 [((535/512),(535/256)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1110_ok T1111_ok
def T1108 : Node := Node.split 1 T1109 T1142
theorem T1108_ok : Node.check D_R11111 T1108 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1109_ok T1142_ok
def T1107 : Node := Node.split 3 T1108 T1197
theorem T1107_ok : Node.check D_R11111 T1107 [((535/512),(535/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1108_ok T1197_ok
def T1106 : Node := Node.leaf L1106
theorem T1106_ok : Node.check D_R11111 T1106 [((535/1024),(535/512)),((2331/1024),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1106_ok
def T1105 : Node := Node.leaf L1105
theorem T1105_ok : Node.check D_R11111 T1105 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1105_ok
def T1104 : Node := Node.leaf L1104
theorem T1104_ok : Node.check D_R11111 T1104 [((1605/2048),(535/512)),((999/512),(4329/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1104_ok
def T1103 : Node := Node.leaf L1103
theorem T1103_ok : Node.check D_R11111 T1103 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1103_ok
def T1102 : Node := Node.leaf L1102
theorem T1102_ok : Node.check D_R11111 T1102 [((3745/4096),(535/512)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L1102_ok
def T1101 : Node := Node.split 1 T1102 T1103
theorem T1101_ok : Node.check D_R11111 T1101 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1102_ok T1103_ok
def T1100 : Node := Node.leaf L1100
theorem T1100_ok : Node.check D_R11111 T1100 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L1100_ok
def T1099 : Node := Node.split 3 T1100 T1101
theorem T1099_ok : Node.check D_R11111 T1099 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1100_ok T1101_ok
def T1098 : Node := Node.leaf L1098
theorem T1098_ok : Node.check D_R11111 T1098 [((1605/2048),(3745/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1098_ok
def T1097 : Node := Node.split 0 T1098 T1099
theorem T1097_ok : Node.check D_R11111 T1097 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1098_ok T1099_ok
def T1096 : Node := Node.split 2 T1097 T1104
theorem T1096_ok : Node.check D_R11111 T1096 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1097_ok T1104_ok
def T1095 : Node := Node.split 1 T1096 T1105
theorem T1095_ok : Node.check D_R11111 T1095 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1096_ok T1105_ok
def T1094 : Node := Node.leaf L1094
theorem T1094_ok : Node.check D_R11111 T1094 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L1094_ok
def T1093 : Node := Node.split 3 T1094 T1095
theorem T1093_ok : Node.check D_R11111 T1093 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1094_ok T1095_ok
def T1092 : Node := Node.leaf L1092
theorem T1092_ok : Node.check D_R11111 T1092 [((535/1024),(1605/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1092_ok
def T1091 : Node := Node.split 0 T1092 T1093
theorem T1091_ok : Node.check D_R11111 T1091 [((535/1024),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1092_ok T1093_ok
def T1090 : Node := Node.leaf L1090
theorem T1090_ok : Node.check D_R11111 T1090 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1090_ok
def T1089 : Node := Node.split 2 T1090 T1091
theorem T1089_ok : Node.check D_R11111 T1089 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1090_ok T1091_ok
def T1088 : Node := Node.split 1 T1089 T1106
theorem T1088_ok : Node.check D_R11111 T1088 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1089_ok T1106_ok
def T1087 : Node := Node.leaf L1087
theorem T1087_ok : Node.check D_R11111 T1087 [((535/1024),(535/512)),((2331/1024),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1087_ok
def T1086 : Node := Node.leaf L1086
theorem T1086_ok : Node.check D_R11111 T1086 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1086_ok
def T1085 : Node := Node.leaf L1085
theorem T1085_ok : Node.check D_R11111 T1085 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1085_ok
def T1084 : Node := Node.leaf L1084
theorem T1084_ok : Node.check D_R11111 T1084 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1084_ok
def T1083 : Node := Node.leaf L1083
theorem T1083_ok : Node.check D_R11111 T1083 [((3745/4096),(535/512)),((8991/4096),(2331/1024)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1083_ok
def T1082 : Node := Node.leaf L1082
theorem T1082_ok : Node.check D_R11111 T1082 [((3745/4096),(535/512)),((4329/2048),(8991/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1082_ok
def T1081 : Node := Node.split 1 T1082 T1083
theorem T1081_ok : Node.check D_R11111 T1081 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1082_ok T1083_ok
def T1080 : Node := Node.split 3 T1081 T1084
theorem T1080_ok : Node.check D_R11111 T1080 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1081_ok T1084_ok
def T1079 : Node := Node.leaf L1079
theorem T1079_ok : Node.check D_R11111 T1079 [((1605/2048),(3745/4096)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1079_ok
def T1078 : Node := Node.split 0 T1079 T1080
theorem T1078_ok : Node.check D_R11111 T1078 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1079_ok T1080_ok
def T1077 : Node := Node.split 2 T1078 T1085
theorem T1077_ok : Node.check D_R11111 T1077 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1078_ok T1085_ok
def T1076 : Node := Node.leaf L1076
theorem T1076_ok : Node.check D_R11111 T1076 [((1605/2048),(535/512)),((999/512),(4329/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1076_ok
def T1075 : Node := Node.leaf L1075
theorem T1075_ok : Node.check D_R11111 T1075 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1075_ok
def T1074 : Node := Node.leaf L1074
theorem T1074_ok : Node.check D_R11111 T1074 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1074_ok
def T1073 : Node := Node.leaf L1073
theorem T1073_ok : Node.check D_R11111 T1073 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1073_ok
def T1072 : Node := Node.split 3 T1073 T1074
theorem T1072_ok : Node.check D_R11111 T1072 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1073_ok T1074_ok
def T1071 : Node := Node.leaf L1071
theorem T1071_ok : Node.check D_R11111 T1071 [((3745/4096),(8025/8192)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1071_ok
def T1070 : Node := Node.split 0 T1071 T1072
theorem T1070_ok : Node.check D_R11111 T1070 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1071_ok T1072_ok
def T1069 : Node := Node.leaf L1069
theorem T1069_ok : Node.check D_R11111 T1069 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1069_ok
def T1068 : Node := Node.leaf L1068
theorem T1068_ok : Node.check D_R11111 T1068 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1068_ok
def T1067 : Node := Node.split 3 T1068 T1069
theorem T1067_ok : Node.check D_R11111 T1067 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1068_ok T1069_ok
def T1066 : Node := Node.leaf L1066
theorem T1066_ok : Node.check D_R11111 T1066 [((3745/4096),(8025/8192)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1066_ok
def T1065 : Node := Node.split 0 T1066 T1067
theorem T1065_ok : Node.check D_R11111 T1065 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1066_ok T1067_ok
def T1064 : Node := Node.split 2 T1065 T1070
theorem T1064_ok : Node.check D_R11111 T1064 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1065_ok T1070_ok
def T1063 : Node := Node.leaf L1063
theorem T1063_ok : Node.check D_R11111 T1063 [((8025/8192),(535/512)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1063_ok
def T1062 : Node := Node.leaf L1062
theorem T1062_ok : Node.check D_R11111 T1062 [((8025/8192),(535/512)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1062_ok
def T1061 : Node := Node.split 3 T1062 T1063
theorem T1061_ok : Node.check D_R11111 T1061 [((8025/8192),(535/512)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1062_ok T1063_ok
def T1060 : Node := Node.leaf L1060
theorem T1060_ok : Node.check D_R11111 T1060 [((3745/4096),(8025/8192)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1060_ok
def T1059 : Node := Node.split 0 T1060 T1061
theorem T1059_ok : Node.check D_R11111 T1059 [((3745/4096),(535/512)),((999/512),(8325/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1060_ok T1061_ok
def T1058 : Node := Node.leaf L1058
theorem T1058_ok : Node.check D_R11111 T1058 [((3745/4096),(535/512)),((999/512),(8325/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1058_ok
def T1057 : Node := Node.split 2 T1058 T1059
theorem T1057_ok : Node.check D_R11111 T1057 [((3745/4096),(535/512)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1058_ok T1059_ok
def T1056 : Node := Node.split 1 T1057 T1064
theorem T1056_ok : Node.check D_R11111 T1056 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1057_ok T1064_ok
def T1055 : Node := Node.split 3 T1056 T1075
theorem T1055_ok : Node.check D_R11111 T1055 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1056_ok T1075_ok
def T1054 : Node := Node.leaf L1054
theorem T1054_ok : Node.check D_R11111 T1054 [((1605/2048),(3745/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1054_ok
def T1053 : Node := Node.split 0 T1054 T1055
theorem T1053_ok : Node.check D_R11111 T1053 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1054_ok T1055_ok
def T1052 : Node := Node.split 2 T1053 T1076
theorem T1052_ok : Node.check D_R11111 T1052 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1053_ok T1076_ok
def T1051 : Node := Node.split 1 T1052 T1077
theorem T1051_ok : Node.check D_R11111 T1051 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1052_ok T1077_ok
def T1050 : Node := Node.split 3 T1051 T1086
theorem T1050_ok : Node.check D_R11111 T1050 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1051_ok T1086_ok
def T1049 : Node := Node.leaf L1049
theorem T1049_ok : Node.check D_R11111 T1049 [((535/1024),(1605/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1049_ok
def T1048 : Node := Node.split 0 T1049 T1050
theorem T1048_ok : Node.check D_R11111 T1048 [((535/1024),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1049_ok T1050_ok
def T1047 : Node := Node.leaf L1047
theorem T1047_ok : Node.check D_R11111 T1047 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1047_ok
def T1046 : Node := Node.split 2 T1047 T1048
theorem T1046_ok : Node.check D_R11111 T1046 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1047_ok T1048_ok
def T1045 : Node := Node.split 1 T1046 T1087
theorem T1045_ok : Node.check D_R11111 T1045 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1046_ok T1087_ok
def T1044 : Node := Node.split 3 T1045 T1088
theorem T1044_ok : Node.check D_R11111 T1044 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1045_ok T1088_ok
def T1043 : Node := Node.leaf L1043
theorem T1043_ok : Node.check D_R11111 T1043 [((0),(535/1024)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1043_ok
def T1042 : Node := Node.split 0 T1043 T1044
theorem T1042_ok : Node.check D_R11111 T1042 [((0),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1043_ok T1044_ok
def T1041 : Node := Node.leaf L1041
theorem T1041_ok : Node.check D_R11111 T1041 [((0),(535/512)),((999/512),(333/128)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1041_ok
def T1040 : Node := Node.split 2 T1041 T1042
theorem T1040_ok : Node.check D_R11111 T1040 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1041_ok T1042_ok
def T1039 : Node := Node.leaf L1039
theorem T1039_ok : Node.check D_R11111 T1039 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L1039_ok
def T1038 : Node := Node.leaf L1038
theorem T1038_ok : Node.check D_R11111 T1038 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L1038_ok
def T1037 : Node := Node.split 3 T1038 T1039
theorem T1037_ok : Node.check D_R11111 T1037 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1038_ok T1039_ok
def T1036 : Node := Node.leaf L1036
theorem T1036_ok : Node.check D_R11111 T1036 [((535/1024),(1605/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1036_ok
def T1035 : Node := Node.split 0 T1036 T1037
theorem T1035_ok : Node.check D_R11111 T1035 [((535/1024),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1036_ok T1037_ok
def T1034 : Node := Node.leaf L1034
theorem T1034_ok : Node.check D_R11111 T1034 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1034_ok
def T1033 : Node := Node.split 2 T1034 T1035
theorem T1033_ok : Node.check D_R11111 T1033 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1034_ok T1035_ok
def T1032 : Node := Node.leaf L1032
theorem T1032_ok : Node.check D_R11111 T1032 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L1032_ok
def T1031 : Node := Node.split 1 T1032 T1033
theorem T1031_ok : Node.check D_R11111 T1031 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1032_ok T1033_ok
def T1030 : Node := Node.leaf L1030
theorem T1030_ok : Node.check D_R11111 T1030 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1030_ok
def T1029 : Node := Node.leaf L1029
theorem T1029_ok : Node.check D_R11111 T1029 [((1605/2048),(535/512)),((3663/2048),(999/512)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1029_ok
def T1028 : Node := Node.leaf L1028
theorem T1028_ok : Node.check D_R11111 T1028 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1028_ok
def T1027 : Node := Node.leaf L1027
theorem T1027_ok : Node.check D_R11111 T1027 [((8025/8192),(535/512)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1027_ok
def T1026 : Node := Node.leaf L1026
theorem T1026_ok : Node.check D_R11111 T1026 [((8025/8192),(535/512)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L1026_ok
def T1025 : Node := Node.split 3 T1026 T1027
theorem T1025_ok : Node.check D_R11111 T1025 [((8025/8192),(535/512)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1026_ok T1027_ok
def T1024 : Node := Node.leaf L1024
theorem T1024_ok : Node.check D_R11111 T1024 [((3745/4096),(8025/8192)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1024_ok
def T1023 : Node := Node.split 0 T1024 T1025
theorem T1023_ok : Node.check D_R11111 T1023 [((3745/4096),(535/512)),((7659/4096),(999/512)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1024_ok T1025_ok
def T1022 : Node := Node.leaf L1022
theorem T1022_ok : Node.check D_R11111 T1022 [((3745/4096),(535/512)),((7659/4096),(999/512)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1022_ok
def T1021 : Node := Node.split 2 T1022 T1023
theorem T1021_ok : Node.check D_R11111 T1021 [((3745/4096),(535/512)),((7659/4096),(999/512)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1022_ok T1023_ok
def T1020 : Node := Node.leaf L1020
theorem T1020_ok : Node.check D_R11111 T1020 [((3745/4096),(535/512)),((3663/2048),(7659/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L1020_ok
def T1019 : Node := Node.split 1 T1020 T1021
theorem T1019_ok : Node.check D_R11111 T1019 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1020_ok T1021_ok
def T1018 : Node := Node.split 3 T1019 T1028
theorem T1018_ok : Node.check D_R11111 T1018 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1019_ok T1028_ok
def T1017 : Node := Node.leaf L1017
theorem T1017_ok : Node.check D_R11111 T1017 [((1605/2048),(3745/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1017_ok
def T1016 : Node := Node.split 0 T1017 T1018
theorem T1016_ok : Node.check D_R11111 T1016 [((1605/2048),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1017_ok T1018_ok
def T1015 : Node := Node.split 2 T1016 T1029
theorem T1015_ok : Node.check D_R11111 T1015 [((1605/2048),(535/512)),((3663/2048),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1016_ok T1029_ok
def T1014 : Node := Node.leaf L1014
theorem T1014_ok : Node.check D_R11111 T1014 [((1605/2048),(535/512)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L1014_ok
def T1013 : Node := Node.split 1 T1014 T1015
theorem T1013_ok : Node.check D_R11111 T1013 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1014_ok T1015_ok
def T1012 : Node := Node.split 3 T1013 T1030
theorem T1012_ok : Node.check D_R11111 T1012 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1013_ok T1030_ok
def T1011 : Node := Node.leaf L1011
theorem T1011_ok : Node.check D_R11111 T1011 [((535/1024),(1605/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1011_ok
def T1010 : Node := Node.split 0 T1011 T1012
theorem T1010_ok : Node.check D_R11111 T1010 [((535/1024),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1011_ok T1012_ok
def T1009 : Node := Node.leaf L1009
theorem T1009_ok : Node.check D_R11111 T1009 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1009_ok
def T1008 : Node := Node.split 2 T1009 T1010
theorem T1008_ok : Node.check D_R11111 T1008 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1009_ok T1010_ok
def T1007 : Node := Node.leaf L1007
theorem T1007_ok : Node.check D_R11111 T1007 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L1007_ok
def T1006 : Node := Node.split 1 T1007 T1008
theorem T1006_ok : Node.check D_R11111 T1006 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1007_ok T1008_ok
def T1005 : Node := Node.split 3 T1006 T1031
theorem T1005_ok : Node.check D_R11111 T1005 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1006_ok T1031_ok
def T1004 : Node := Node.leaf L1004
theorem T1004_ok : Node.check D_R11111 T1004 [((0),(535/1024)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1004_ok
def T1003 : Node := Node.split 0 T1004 T1005
theorem T1003_ok : Node.check D_R11111 T1003 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1004_ok T1005_ok
def T1002 : Node := Node.leaf L1002
theorem T1002_ok : Node.check D_R11111 T1002 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L1002_ok
def T1001 : Node := Node.split 2 T1002 T1003
theorem T1001_ok : Node.check D_R11111 T1001 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1002_ok T1003_ok
def T1000 : Node := Node.split 1 T1001 T1040
theorem T1000_ok : Node.check D_R11111 T1000 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1001_ok T1040_ok
def T999 : Node := Node.leaf L999
theorem T999_ok : Node.check D_R11111 T999 [((535/1024),(535/512)),((2331/1024),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L999_ok
def T998 : Node := Node.leaf L998
theorem T998_ok : Node.check D_R11111 T998 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L998_ok
def T997 : Node := Node.leaf L997
theorem T997_ok : Node.check D_R11111 T997 [((3745/4096),(535/512)),((8991/4096),(2331/1024)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L997_ok
def T996 : Node := Node.leaf L996
theorem T996_ok : Node.check D_R11111 T996 [((3745/4096),(535/512)),((4329/2048),(8991/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L996_ok
def T995 : Node := Node.split 1 T996 T997
theorem T995_ok : Node.check D_R11111 T995 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T996_ok T997_ok
def T994 : Node := Node.leaf L994
theorem T994_ok : Node.check D_R11111 T994 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L994_ok
def T993 : Node := Node.split 3 T994 T995
theorem T993_ok : Node.check D_R11111 T993 [((3745/4096),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T994_ok T995_ok
def T992 : Node := Node.leaf L992
theorem T992_ok : Node.check D_R11111 T992 [((1605/2048),(3745/4096)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L992_ok
def T991 : Node := Node.split 0 T992 T993
theorem T991_ok : Node.check D_R11111 T991 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T992_ok T993_ok
def T990 : Node := Node.split 2 T991 T998
theorem T990_ok : Node.check D_R11111 T990 [((1605/2048),(535/512)),((4329/2048),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T991_ok T998_ok
def T989 : Node := Node.leaf L989
theorem T989_ok : Node.check D_R11111 T989 [((1605/2048),(535/512)),((999/512),(4329/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L989_ok
def T988 : Node := Node.leaf L988
theorem T988_ok : Node.check D_R11111 T988 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L988_ok
def T987 : Node := Node.leaf L987
theorem T987_ok : Node.check D_R11111 T987 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L987_ok
def T986 : Node := Node.split 3 T987 T988
theorem T986_ok : Node.check D_R11111 T986 [((8025/8192),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T987_ok T988_ok
def T985 : Node := Node.leaf L985
theorem T985_ok : Node.check D_R11111 T985 [((3745/4096),(8025/8192)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L985_ok
def T984 : Node := Node.split 0 T985 T986
theorem T984_ok : Node.check D_R11111 T984 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T985_ok T986_ok
def T983 : Node := Node.leaf L983
theorem T983_ok : Node.check D_R11111 T983 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L983_ok
def T982 : Node := Node.split 2 T983 T984
theorem T982_ok : Node.check D_R11111 T982 [((3745/4096),(535/512)),((8325/4096),(4329/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T983_ok T984_ok
def T981 : Node := Node.leaf L981
theorem T981_ok : Node.check D_R11111 T981 [((3745/4096),(535/512)),((999/512),(8325/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L981_ok
def T980 : Node := Node.split 1 T981 T982
theorem T980_ok : Node.check D_R11111 T980 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T981_ok T982_ok
def T979 : Node := Node.leaf L979
theorem T979_ok : Node.check D_R11111 T979 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L979_ok
def T978 : Node := Node.split 3 T979 T980
theorem T978_ok : Node.check D_R11111 T978 [((3745/4096),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T979_ok T980_ok
def T977 : Node := Node.leaf L977
theorem T977_ok : Node.check D_R11111 T977 [((1605/2048),(3745/4096)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L977_ok
def T976 : Node := Node.split 0 T977 T978
theorem T976_ok : Node.check D_R11111 T976 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T977_ok T978_ok
def T975 : Node := Node.split 2 T976 T989
theorem T975_ok : Node.check D_R11111 T975 [((1605/2048),(535/512)),((999/512),(4329/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T976_ok T989_ok
def T974 : Node := Node.split 1 T975 T990
theorem T974_ok : Node.check D_R11111 T974 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T975_ok T990_ok
def T973 : Node := Node.leaf L973
theorem T973_ok : Node.check D_R11111 T973 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L973_ok
def T972 : Node := Node.split 3 T973 T974
theorem T972_ok : Node.check D_R11111 T972 [((1605/2048),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T973_ok T974_ok
def T971 : Node := Node.leaf L971
theorem T971_ok : Node.check D_R11111 T971 [((535/1024),(1605/2048)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L971_ok
def T970 : Node := Node.split 0 T971 T972
theorem T970_ok : Node.check D_R11111 T970 [((535/1024),(535/512)),((999/512),(2331/1024)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T971_ok T972_ok
def T969 : Node := Node.leaf L969
theorem T969_ok : Node.check D_R11111 T969 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L969_ok
def T968 : Node := Node.split 2 T969 T970
theorem T968_ok : Node.check D_R11111 T968 [((535/1024),(535/512)),((999/512),(2331/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T969_ok T970_ok
def T967 : Node := Node.split 1 T968 T999
theorem T967_ok : Node.check D_R11111 T967 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T968_ok T999_ok
def T966 : Node := Node.leaf L966
theorem T966_ok : Node.check D_R11111 T966 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L966_ok
def T965 : Node := Node.split 3 T966 T967
theorem T965_ok : Node.check D_R11111 T965 [((535/1024),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T966_ok T967_ok
def T964 : Node := Node.leaf L964
theorem T964_ok : Node.check D_R11111 T964 [((0),(535/1024)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L964_ok
def T963 : Node := Node.split 0 T964 T965
theorem T963_ok : Node.check D_R11111 T963 [((0),(535/512)),((999/512),(333/128)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T964_ok T965_ok
def T962 : Node := Node.leaf L962
theorem T962_ok : Node.check D_R11111 T962 [((0),(535/512)),((999/512),(333/128)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L962_ok
def T961 : Node := Node.split 2 T962 T963
theorem T961_ok : Node.check D_R11111 T961 [((0),(535/512)),((999/512),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T962_ok T963_ok
def T960 : Node := Node.leaf L960
theorem T960_ok : Node.check D_R11111 T960 [((1605/2048),(535/512)),((3663/2048),(999/512)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L960_ok
def T959 : Node := Node.leaf L959
theorem T959_ok : Node.check D_R11111 T959 [((3745/4096),(535/512)),((7659/4096),(999/512)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L959_ok
def T958 : Node := Node.leaf L958
theorem T958_ok : Node.check D_R11111 T958 [((3745/4096),(535/512)),((3663/2048),(7659/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L958_ok
def T957 : Node := Node.split 1 T958 T959
theorem T957_ok : Node.check D_R11111 T957 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T958_ok T959_ok
def T956 : Node := Node.leaf L956
theorem T956_ok : Node.check D_R11111 T956 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L956_ok
def T955 : Node := Node.split 3 T956 T957
theorem T955_ok : Node.check D_R11111 T955 [((3745/4096),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T956_ok T957_ok
def T954 : Node := Node.leaf L954
theorem T954_ok : Node.check D_R11111 T954 [((1605/2048),(3745/4096)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L954_ok
def T953 : Node := Node.split 0 T954 T955
theorem T953_ok : Node.check D_R11111 T953 [((1605/2048),(535/512)),((3663/2048),(999/512)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T954_ok T955_ok
def T952 : Node := Node.split 2 T953 T960
theorem T952_ok : Node.check D_R11111 T952 [((1605/2048),(535/512)),((3663/2048),(999/512)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T953_ok T960_ok
def T951 : Node := Node.leaf L951
theorem T951_ok : Node.check D_R11111 T951 [((1605/2048),(535/512)),((1665/1024),(3663/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L951_ok
def T950 : Node := Node.split 1 T951 T952
theorem T950_ok : Node.check D_R11111 T950 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T951_ok T952_ok
def T949 : Node := Node.leaf L949
theorem T949_ok : Node.check D_R11111 T949 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L949_ok
def T948 : Node := Node.split 3 T949 T950
theorem T948_ok : Node.check D_R11111 T948 [((1605/2048),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T949_ok T950_ok
def T947 : Node := Node.leaf L947
theorem T947_ok : Node.check D_R11111 T947 [((535/1024),(1605/2048)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L947_ok
def T946 : Node := Node.split 0 T947 T948
theorem T946_ok : Node.check D_R11111 T946 [((535/1024),(535/512)),((1665/1024),(999/512)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T947_ok T948_ok
def T945 : Node := Node.leaf L945
theorem T945_ok : Node.check D_R11111 T945 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L945_ok
def T944 : Node := Node.split 2 T945 T946
theorem T944_ok : Node.check D_R11111 T944 [((535/1024),(535/512)),((1665/1024),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T945_ok T946_ok
def T943 : Node := Node.leaf L943
theorem T943_ok : Node.check D_R11111 T943 [((535/1024),(535/512)),((333/256),(1665/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L943_ok
def T942 : Node := Node.split 1 T943 T944
theorem T942_ok : Node.check D_R11111 T942 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T943_ok T944_ok
def T941 : Node := Node.leaf L941
theorem T941_ok : Node.check D_R11111 T941 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L941_ok
def T940 : Node := Node.split 3 T941 T942
theorem T940_ok : Node.check D_R11111 T940 [((535/1024),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T941_ok T942_ok
def T939 : Node := Node.leaf L939
theorem T939_ok : Node.check D_R11111 T939 [((0),(535/1024)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L939_ok
def T938 : Node := Node.split 0 T939 T940
theorem T938_ok : Node.check D_R11111 T938 [((0),(535/512)),((333/256),(999/512)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T939_ok T940_ok
def T937 : Node := Node.leaf L937
theorem T937_ok : Node.check D_R11111 T937 [((0),(535/512)),((333/256),(999/512)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L937_ok
def T936 : Node := Node.split 2 T937 T938
theorem T936_ok : Node.check D_R11111 T936 [((0),(535/512)),((333/256),(999/512)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T937_ok T938_ok
def T935 : Node := Node.split 1 T936 T961
theorem T935_ok : Node.check D_R11111 T935 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T936_ok T961_ok
def T934 : Node := Node.split 3 T935 T1000
theorem T934_ok : Node.check D_R11111 T934 [((0),(535/512)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T935_ok T1000_ok
def T933 : Node := Node.split 0 T934 T1107
theorem T933_ok : Node.check D_R11111 T933 [((0),(535/256)),((333/256),(333/128)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T934_ok T1107_ok
def T932 : Node := Node.split 2 T933 T1358
theorem T932_ok : Node.check D_R11111 T932 [((0),(535/256)),((333/256),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T933_ok T1358_ok
def T931 : Node := Node.leaf L931
theorem T931_ok : Node.check D_R11111 T931 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L931_ok
def T930 : Node := Node.leaf L930
theorem T930_ok : Node.check D_R11111 T930 [((1605/1024),(535/256)),((333/512),(999/1024)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L930_ok
def T929 : Node := Node.split 1 T930 T931
theorem T929_ok : Node.check D_R11111 T929 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T930_ok T931_ok
def T928 : Node := Node.leaf L928
theorem T928_ok : Node.check D_R11111 T928 [((1605/1024),(535/256)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L928_ok
def T927 : Node := Node.leaf L927
theorem T927_ok : Node.check D_R11111 T927 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L927_ok
def T926 : Node := Node.leaf L926
theorem T926_ok : Node.check D_R11111 T926 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L926_ok
def T925 : Node := Node.leaf L925
theorem T925_ok : Node.check D_R11111 T925 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L925_ok
def T924 : Node := Node.leaf L924
theorem T924_ok : Node.check D_R11111 T924 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L924_ok
def T923 : Node := Node.leaf L923
theorem T923_ok : Node.check D_R11111 T923 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L923_ok
def T922 : Node := Node.leaf L922
theorem T922_ok : Node.check D_R11111 T922 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L922_ok
def T921 : Node := Node.leaf L921
theorem T921_ok : Node.check D_R11111 T921 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L921_ok
def T920 : Node := Node.split 3 T921 T922
theorem T920_ok : Node.check D_R11111 T920 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T921_ok T922_ok
def T919 : Node := Node.leaf L919
theorem T919_ok : Node.check D_R11111 T919 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L919_ok
def T918 : Node := Node.leaf L918
theorem T918_ok : Node.check D_R11111 T918 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L918_ok
def T917 : Node := Node.split 3 T918 T919
theorem T917_ok : Node.check D_R11111 T917 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T918_ok T919_ok
def T916 : Node := Node.split 0 T917 T920
theorem T916_ok : Node.check D_R11111 T916 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T917_ok T920_ok
def T915 : Node := Node.split 2 T916 T923
theorem T915_ok : Node.check D_R11111 T915 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T916_ok T923_ok
def T914 : Node := Node.leaf L914
theorem T914_ok : Node.check D_R11111 T914 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L914_ok
def T913 : Node := Node.leaf L913
theorem T913_ok : Node.check D_R11111 T913 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L913_ok
def T912 : Node := Node.split 2 T913 T914
theorem T912_ok : Node.check D_R11111 T912 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T913_ok T914_ok
def T911 : Node := Node.split 1 T912 T915
theorem T911_ok : Node.check D_R11111 T911 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T912_ok T915_ok
def T910 : Node := Node.split 3 T911 T924
theorem T910_ok : Node.check D_R11111 T910 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T911_ok T924_ok
def T909 : Node := Node.leaf L909
theorem T909_ok : Node.check D_R11111 T909 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L909_ok
def T908 : Node := Node.leaf L908
theorem T908_ok : Node.check D_R11111 T908 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L908_ok
def T907 : Node := Node.leaf L907
theorem T907_ok : Node.check D_R11111 T907 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L907_ok
def T906 : Node := Node.split 2 T907 T908
theorem T906_ok : Node.check D_R11111 T906 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T907_ok T908_ok
def T905 : Node := Node.leaf L905
theorem T905_ok : Node.check D_R11111 T905 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L905_ok
def T904 : Node := Node.split 1 T905 T906
theorem T904_ok : Node.check D_R11111 T904 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T905_ok T906_ok
def T903 : Node := Node.split 3 T904 T909
theorem T903_ok : Node.check D_R11111 T903 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T904_ok T909_ok
def T902 : Node := Node.split 0 T903 T910
theorem T902_ok : Node.check D_R11111 T902 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T903_ok T910_ok
def T901 : Node := Node.split 2 T902 T925
theorem T901_ok : Node.check D_R11111 T901 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T902_ok T925_ok
def T900 : Node := Node.split 1 T901 T926
theorem T900_ok : Node.check D_R11111 T900 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T901_ok T926_ok
def T899 : Node := Node.split 3 T900 T927
theorem T899_ok : Node.check D_R11111 T899 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T900_ok T927_ok
def T898 : Node := Node.leaf L898
theorem T898_ok : Node.check D_R11111 T898 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L898_ok
def T897 : Node := Node.split 0 T898 T899
theorem T897_ok : Node.check D_R11111 T897 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T898_ok T899_ok
def T896 : Node := Node.split 2 T897 T928
theorem T896_ok : Node.check D_R11111 T896 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T897_ok T928_ok
def T895 : Node := Node.leaf L895
theorem T895_ok : Node.check D_R11111 T895 [((1605/1024),(535/256)),((333/512),(999/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L895_ok
def T894 : Node := Node.split 1 T895 T896
theorem T894_ok : Node.check D_R11111 T894 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T895_ok T896_ok
def T893 : Node := Node.split 3 T894 T929
theorem T893_ok : Node.check D_R11111 T893 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T894_ok T929_ok
def T892 : Node := Node.leaf L892
theorem T892_ok : Node.check D_R11111 T892 [((535/512),(1605/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L892_ok
def T891 : Node := Node.leaf L891
theorem T891_ok : Node.check D_R11111 T891 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L891_ok
def T890 : Node := Node.leaf L890
theorem T890_ok : Node.check D_R11111 T890 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L890_ok
def T889 : Node := Node.leaf L889
theorem T889_ok : Node.check D_R11111 T889 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L889_ok
def T888 : Node := Node.leaf L888
theorem T888_ok : Node.check D_R11111 T888 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L888_ok
def T887 : Node := Node.leaf L887
theorem T887_ok : Node.check D_R11111 T887 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L887_ok
def T886 : Node := Node.leaf L886
theorem T886_ok : Node.check D_R11111 T886 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L886_ok
def T885 : Node := Node.split 2 T886 T887
theorem T885_ok : Node.check D_R11111 T885 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T886_ok T887_ok
def T884 : Node := Node.leaf L884
theorem T884_ok : Node.check D_R11111 T884 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L884_ok
def T883 : Node := Node.split 1 T884 T885
theorem T883_ok : Node.check D_R11111 T883 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T884_ok T885_ok
def T882 : Node := Node.leaf L882
theorem T882_ok : Node.check D_R11111 T882 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L882_ok
def T881 : Node := Node.leaf L881
theorem T881_ok : Node.check D_R11111 T881 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L881_ok
def T880 : Node := Node.split 1 T881 T882
theorem T880_ok : Node.check D_R11111 T880 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T881_ok T882_ok
def T879 : Node := Node.split 3 T880 T883
theorem T879_ok : Node.check D_R11111 T879 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T880_ok T883_ok
def T878 : Node := Node.split 0 T879 T888
theorem T878_ok : Node.check D_R11111 T878 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T879_ok T888_ok
def T877 : Node := Node.split 2 T878 T889
theorem T877_ok : Node.check D_R11111 T877 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T878_ok T889_ok
def T876 : Node := Node.split 1 T877 T890
theorem T876_ok : Node.check D_R11111 T876 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T877_ok T890_ok
def T875 : Node := Node.leaf L875
theorem T875_ok : Node.check D_R11111 T875 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L875_ok
def T874 : Node := Node.split 3 T875 T876
theorem T874_ok : Node.check D_R11111 T874 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T875_ok T876_ok
def T873 : Node := Node.split 0 T874 T891
theorem T873_ok : Node.check D_R11111 T873 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T874_ok T891_ok
def T872 : Node := Node.split 2 T873 T892
theorem T872_ok : Node.check D_R11111 T872 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T873_ok T892_ok
def T871 : Node := Node.leaf L871
theorem T871_ok : Node.check D_R11111 T871 [((535/512),(1605/1024)),((333/512),(999/1024)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L871_ok
def T870 : Node := Node.split 1 T871 T872
theorem T870_ok : Node.check D_R11111 T870 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T871_ok T872_ok
def T869 : Node := Node.leaf L869
theorem T869_ok : Node.check D_R11111 T869 [((535/512),(1605/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L869_ok
def T868 : Node := Node.leaf L868
theorem T868_ok : Node.check D_R11111 T868 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L868_ok
def T867 : Node := Node.leaf L867
theorem T867_ok : Node.check D_R11111 T867 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L867_ok
def T866 : Node := Node.leaf L866
theorem T866_ok : Node.check D_R11111 T866 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L866_ok
def T865 : Node := Node.leaf L865
theorem T865_ok : Node.check D_R11111 T865 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L865_ok
def T864 : Node := Node.leaf L864
theorem T864_ok : Node.check D_R11111 T864 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L864_ok
def T863 : Node := Node.leaf L863
theorem T863_ok : Node.check D_R11111 T863 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L863_ok
def T862 : Node := Node.leaf L862
theorem T862_ok : Node.check D_R11111 T862 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L862_ok
def T861 : Node := Node.leaf L861
theorem T861_ok : Node.check D_R11111 T861 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L861_ok
def T860 : Node := Node.leaf L860
theorem T860_ok : Node.check D_R11111 T860 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L860_ok
def T859 : Node := Node.leaf L859
theorem T859_ok : Node.check D_R11111 T859 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L859_ok
def T858 : Node := Node.split 3 T859 T860
theorem T858_ok : Node.check D_R11111 T858 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T859_ok T860_ok
def T857 : Node := Node.split 0 T858 T861
theorem T857_ok : Node.check D_R11111 T857 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T858_ok T861_ok
def T856 : Node := Node.split 2 T857 T862
theorem T856_ok : Node.check D_R11111 T856 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T857_ok T862_ok
def T855 : Node := Node.leaf L855
theorem T855_ok : Node.check D_R11111 T855 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L855_ok
def T854 : Node := Node.leaf L854
theorem T854_ok : Node.check D_R11111 T854 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L854_ok
def T853 : Node := Node.leaf L853
theorem T853_ok : Node.check D_R11111 T853 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L853_ok
def T852 : Node := Node.split 3 T853 T854
theorem T852_ok : Node.check D_R11111 T852 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T853_ok T854_ok
def T851 : Node := Node.split 0 T852 T855
theorem T851_ok : Node.check D_R11111 T851 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T852_ok T855_ok
def T850 : Node := Node.leaf L850
theorem T850_ok : Node.check D_R11111 T850 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L850_ok
def T849 : Node := Node.leaf L849
theorem T849_ok : Node.check D_R11111 T849 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L849_ok
def T848 : Node := Node.split 0 T849 T850
theorem T848_ok : Node.check D_R11111 T848 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T849_ok T850_ok
def T847 : Node := Node.split 2 T848 T851
theorem T847_ok : Node.check D_R11111 T847 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T848_ok T851_ok
def T846 : Node := Node.split 1 T847 T856
theorem T846_ok : Node.check D_R11111 T846 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T847_ok T856_ok
def T845 : Node := Node.split 3 T846 T863
theorem T845_ok : Node.check D_R11111 T845 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T846_ok T863_ok
def T844 : Node := Node.split 0 T845 T864
theorem T844_ok : Node.check D_R11111 T844 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T845_ok T864_ok
def T843 : Node := Node.split 2 T844 T865
theorem T843_ok : Node.check D_R11111 T843 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T844_ok T865_ok
def T842 : Node := Node.split 1 T843 T866
theorem T842_ok : Node.check D_R11111 T842 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T843_ok T866_ok
def T841 : Node := Node.split 3 T842 T867
theorem T841_ok : Node.check D_R11111 T841 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T842_ok T867_ok
def T840 : Node := Node.split 0 T841 T868
theorem T840_ok : Node.check D_R11111 T840 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T841_ok T868_ok
def T839 : Node := Node.split 2 T840 T869
theorem T839_ok : Node.check D_R11111 T839 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T840_ok T869_ok
def T838 : Node := Node.leaf L838
theorem T838_ok : Node.check D_R11111 T838 [((535/512),(1605/1024)),((333/512),(999/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L838_ok
def T837 : Node := Node.split 1 T838 T839
theorem T837_ok : Node.check D_R11111 T837 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T838_ok T839_ok
def T836 : Node := Node.split 3 T837 T870
theorem T836_ok : Node.check D_R11111 T836 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T837_ok T870_ok
def T835 : Node := Node.split 0 T836 T893
theorem T835_ok : Node.check D_R11111 T835 [((535/512),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T836_ok T893_ok
def T834 : Node := Node.leaf L834
theorem T834_ok : Node.check D_R11111 T834 [((1605/1024),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L834_ok
def T833 : Node := Node.leaf L833
theorem T833_ok : Node.check D_R11111 T833 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(1665/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L833_ok
def T832 : Node := Node.split 2 T833 T834
theorem T832_ok : Node.check D_R11111 T832 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T833_ok T834_ok
def T831 : Node := Node.leaf L831
theorem T831_ok : Node.check D_R11111 T831 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L831_ok
def T830 : Node := Node.split 1 T831 T832
theorem T830_ok : Node.check D_R11111 T830 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T831_ok T832_ok
def T829 : Node := Node.leaf L829
theorem T829_ok : Node.check D_R11111 T829 [((3745/2048),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L829_ok
def T828 : Node := Node.leaf L828
theorem T828_ok : Node.check D_R11111 T828 [((3745/2048),(535/256)),((2331/2048),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L828_ok
def T827 : Node := Node.leaf L827
theorem T827_ok : Node.check D_R11111 T827 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L827_ok
def T826 : Node := Node.split 1 T827 T828
theorem T826_ok : Node.check D_R11111 T826 [((3745/2048),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T827_ok T828_ok
def T825 : Node := Node.split 3 T826 T829
theorem T825_ok : Node.check D_R11111 T825 [((3745/2048),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T826_ok T829_ok
def T824 : Node := Node.leaf L824
theorem T824_ok : Node.check D_R11111 T824 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L824_ok
def T823 : Node := Node.split 0 T824 T825
theorem T823_ok : Node.check D_R11111 T823 [((1605/1024),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T824_ok T825_ok
def T822 : Node := Node.leaf L822
theorem T822_ok : Node.check D_R11111 T822 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L822_ok
def T821 : Node := Node.split 2 T822 T823
theorem T821_ok : Node.check D_R11111 T821 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T822_ok T823_ok
def T820 : Node := Node.leaf L820
theorem T820_ok : Node.check D_R11111 T820 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L820_ok
def T819 : Node := Node.split 1 T820 T821
theorem T819_ok : Node.check D_R11111 T819 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T820_ok T821_ok
def T818 : Node := Node.split 3 T819 T830
theorem T818_ok : Node.check D_R11111 T818 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T819_ok T830_ok
def T817 : Node := Node.leaf L817
theorem T817_ok : Node.check D_R11111 T817 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L817_ok
def T816 : Node := Node.leaf L816
theorem T816_ok : Node.check D_R11111 T816 [((535/512),(2675/2048)),((2331/2048),(333/256)),((1665/1024),(999/512)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L816_ok
def T815 : Node := Node.leaf L815
theorem T815_ok : Node.check D_R11111 T815 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L815_ok
def T814 : Node := Node.leaf L814
theorem T814_ok : Node.check D_R11111 T814 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(3663/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L814_ok
def T813 : Node := Node.split 2 T814 T815
theorem T813_ok : Node.check D_R11111 T813 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T814_ok T815_ok
def T812 : Node := Node.split 1 T813 T816
theorem T812_ok : Node.check D_R11111 T812 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T813_ok T816_ok
def T811 : Node := Node.leaf L811
theorem T811_ok : Node.check D_R11111 T811 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L811_ok
def T810 : Node := Node.split 3 T811 T812
theorem T810_ok : Node.check D_R11111 T810 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T811_ok T812_ok
def T809 : Node := Node.split 0 T810 T817
theorem T809_ok : Node.check D_R11111 T809 [((535/512),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T810_ok T817_ok
def T808 : Node := Node.leaf L808
theorem T808_ok : Node.check D_R11111 T808 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L808_ok
def T807 : Node := Node.split 2 T808 T809
theorem T807_ok : Node.check D_R11111 T807 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T808_ok T809_ok
def T806 : Node := Node.leaf L806
theorem T806_ok : Node.check D_R11111 T806 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L806_ok
def T805 : Node := Node.split 1 T806 T807
theorem T805_ok : Node.check D_R11111 T805 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T806_ok T807_ok
def T804 : Node := Node.leaf L804
theorem T804_ok : Node.check D_R11111 T804 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L804_ok
def T803 : Node := Node.leaf L803
theorem T803_ok : Node.check D_R11111 T803 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L803_ok
def T802 : Node := Node.leaf L802
theorem T802_ok : Node.check D_R11111 T802 [((535/512),(2675/2048)),((2331/2048),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L802_ok
def T801 : Node := Node.leaf L801
theorem T801_ok : Node.check D_R11111 T801 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L801_ok
def T800 : Node := Node.leaf L800
theorem T800_ok : Node.check D_R11111 T800 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L800_ok
def T799 : Node := Node.leaf L799
theorem T799_ok : Node.check D_R11111 T799 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L799_ok
def T798 : Node := Node.leaf L798
theorem T798_ok : Node.check D_R11111 T798 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L798_ok
def T797 : Node := Node.split 0 T798 T799
theorem T797_ok : Node.check D_R11111 T797 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T798_ok T799_ok
def T796 : Node := Node.leaf L796
theorem T796_ok : Node.check D_R11111 T796 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((3663/2048),(7659/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L796_ok
def T795 : Node := Node.split 2 T796 T797
theorem T795_ok : Node.check D_R11111 T795 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T796_ok T797_ok
def T794 : Node := Node.leaf L794
theorem T794_ok : Node.check D_R11111 T794 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L794_ok
def T793 : Node := Node.split 1 T794 T795
theorem T793_ok : Node.check D_R11111 T793 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T794_ok T795_ok
def T792 : Node := Node.split 3 T793 T800
theorem T792_ok : Node.check D_R11111 T792 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T793_ok T800_ok
def T791 : Node := Node.split 0 T792 T801
theorem T791_ok : Node.check D_R11111 T791 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T792_ok T801_ok
def T790 : Node := Node.leaf L790
theorem T790_ok : Node.check D_R11111 T790 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(3663/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L790_ok
def T789 : Node := Node.split 2 T790 T791
theorem T789_ok : Node.check D_R11111 T789 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T790_ok T791_ok
def T788 : Node := Node.split 1 T789 T802
theorem T788_ok : Node.check D_R11111 T788 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T789_ok T802_ok
def T787 : Node := Node.split 3 T788 T803
theorem T787_ok : Node.check D_R11111 T787 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T788_ok T803_ok
def T786 : Node := Node.split 0 T787 T804
theorem T786_ok : Node.check D_R11111 T786 [((535/512),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T787_ok T804_ok
def T785 : Node := Node.leaf L785
theorem T785_ok : Node.check D_R11111 T785 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L785_ok
def T784 : Node := Node.split 2 T785 T786
theorem T784_ok : Node.check D_R11111 T784 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T785_ok T786_ok
def T783 : Node := Node.leaf L783
theorem T783_ok : Node.check D_R11111 T783 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L783_ok
def T782 : Node := Node.split 1 T783 T784
theorem T782_ok : Node.check D_R11111 T782 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T783_ok T784_ok
def T781 : Node := Node.split 3 T782 T805
theorem T781_ok : Node.check D_R11111 T781 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T782_ok T805_ok
def T780 : Node := Node.split 0 T781 T818
theorem T780_ok : Node.check D_R11111 T780 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T781_ok T818_ok
def T779 : Node := Node.split 2 T780 T835
theorem T779_ok : Node.check D_R11111 T779 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T780_ok T835_ok
def T778 : Node := Node.leaf L778
theorem T778_ok : Node.check D_R11111 T778 [((535/512),(535/256)),((0),(333/512)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L778_ok
def T777 : Node := Node.split 1 T778 T779
theorem T777_ok : Node.check D_R11111 T777 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T778_ok T779_ok
def T776 : Node := Node.leaf L776
theorem T776_ok : Node.check D_R11111 T776 [((1605/1024),(535/256)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L776_ok
def T775 : Node := Node.leaf L775
theorem T775_ok : Node.check D_R11111 T775 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L775_ok
def T774 : Node := Node.leaf L774
theorem T774_ok : Node.check D_R11111 T774 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L774_ok
def T773 : Node := Node.leaf L773
theorem T773_ok : Node.check D_R11111 T773 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L773_ok
def T772 : Node := Node.leaf L772
theorem T772_ok : Node.check D_R11111 T772 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L772_ok
def T771 : Node := Node.split 2 T772 T773
theorem T771_ok : Node.check D_R11111 T771 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T772_ok T773_ok
def T770 : Node := Node.leaf L770
theorem T770_ok : Node.check D_R11111 T770 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L770_ok
def T769 : Node := Node.split 1 T770 T771
theorem T769_ok : Node.check D_R11111 T769 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T770_ok T771_ok
def T768 : Node := Node.leaf L768
theorem T768_ok : Node.check D_R11111 T768 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L768_ok
def T767 : Node := Node.split 3 T768 T769
theorem T767_ok : Node.check D_R11111 T767 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T768_ok T769_ok
def T766 : Node := Node.leaf L766
theorem T766_ok : Node.check D_R11111 T766 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L766_ok
def T765 : Node := Node.split 0 T766 T767
theorem T765_ok : Node.check D_R11111 T765 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T766_ok T767_ok
def T764 : Node := Node.split 2 T765 T774
theorem T764_ok : Node.check D_R11111 T764 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T765_ok T774_ok
def T763 : Node := Node.split 1 T764 T775
theorem T763_ok : Node.check D_R11111 T763 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T764_ok T775_ok
def T762 : Node := Node.leaf L762
theorem T762_ok : Node.check D_R11111 T762 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L762_ok
def T761 : Node := Node.split 3 T762 T763
theorem T761_ok : Node.check D_R11111 T761 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T762_ok T763_ok
def T760 : Node := Node.leaf L760
theorem T760_ok : Node.check D_R11111 T760 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L760_ok
def T759 : Node := Node.split 0 T760 T761
theorem T759_ok : Node.check D_R11111 T759 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T760_ok T761_ok
def T758 : Node := Node.split 2 T759 T776
theorem T758_ok : Node.check D_R11111 T758 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T759_ok T776_ok
def T757 : Node := Node.leaf L757
theorem T757_ok : Node.check D_R11111 T757 [((1605/1024),(535/256)),((333/512),(999/1024)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L757_ok
def T756 : Node := Node.split 1 T757 T758
theorem T756_ok : Node.check D_R11111 T756 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T757_ok T758_ok
def T755 : Node := Node.leaf L755
theorem T755_ok : Node.check D_R11111 T755 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L755_ok
def T754 : Node := Node.split 3 T755 T756
theorem T754_ok : Node.check D_R11111 T754 [((1605/1024),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T755_ok T756_ok
def T753 : Node := Node.leaf L753
theorem T753_ok : Node.check D_R11111 T753 [((535/512),(1605/1024)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L753_ok
def T752 : Node := Node.leaf L752
theorem T752_ok : Node.check D_R11111 T752 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L752_ok
def T751 : Node := Node.leaf L751
theorem T751_ok : Node.check D_R11111 T751 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L751_ok
def T750 : Node := Node.leaf L750
theorem T750_ok : Node.check D_R11111 T750 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L750_ok
def T749 : Node := Node.leaf L749
theorem T749_ok : Node.check D_R11111 T749 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L749_ok
def T748 : Node := Node.leaf L748
theorem T748_ok : Node.check D_R11111 T748 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L748_ok
def T747 : Node := Node.split 1 T748 T749
theorem T747_ok : Node.check D_R11111 T747 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T748_ok T749_ok
def T746 : Node := Node.leaf L746
theorem T746_ok : Node.check D_R11111 T746 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L746_ok
def T745 : Node := Node.split 3 T746 T747
theorem T745_ok : Node.check D_R11111 T745 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T746_ok T747_ok
def T744 : Node := Node.split 0 T745 T750
theorem T744_ok : Node.check D_R11111 T744 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T745_ok T750_ok
def T743 : Node := Node.leaf L743
theorem T743_ok : Node.check D_R11111 T743 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L743_ok
def T742 : Node := Node.leaf L742
theorem T742_ok : Node.check D_R11111 T742 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L742_ok
def T741 : Node := Node.leaf L741
theorem T741_ok : Node.check D_R11111 T741 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L741_ok
def T740 : Node := Node.leaf L740
theorem T740_ok : Node.check D_R11111 T740 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L740_ok
def T739 : Node := Node.split 3 T740 T741
theorem T739_ok : Node.check D_R11111 T739 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T740_ok T741_ok
def T738 : Node := Node.split 0 T739 T742
theorem T738_ok : Node.check D_R11111 T738 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T739_ok T742_ok
def T737 : Node := Node.leaf L737
theorem T737_ok : Node.check D_R11111 T737 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L737_ok
def T736 : Node := Node.leaf L736
theorem T736_ok : Node.check D_R11111 T736 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L736_ok
def T735 : Node := Node.split 0 T736 T737
theorem T735_ok : Node.check D_R11111 T735 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T736_ok T737_ok
def T734 : Node := Node.split 2 T735 T738
theorem T734_ok : Node.check D_R11111 T734 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T735_ok T738_ok
def T733 : Node := Node.leaf L733
theorem T733_ok : Node.check D_R11111 T733 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L733_ok
def T732 : Node := Node.leaf L732
theorem T732_ok : Node.check D_R11111 T732 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L732_ok
def T731 : Node := Node.split 0 T732 T733
theorem T731_ok : Node.check D_R11111 T731 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T732_ok T733_ok
def T730 : Node := Node.leaf L730
theorem T730_ok : Node.check D_R11111 T730 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L730_ok
def T729 : Node := Node.split 2 T730 T731
theorem T729_ok : Node.check D_R11111 T729 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T730_ok T731_ok
def T728 : Node := Node.split 1 T729 T734
theorem T728_ok : Node.check D_R11111 T728 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T729_ok T734_ok
def T727 : Node := Node.leaf L727
theorem T727_ok : Node.check D_R11111 T727 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L727_ok
def T726 : Node := Node.split 3 T727 T728
theorem T726_ok : Node.check D_R11111 T726 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T727_ok T728_ok
def T725 : Node := Node.split 0 T726 T743
theorem T725_ok : Node.check D_R11111 T725 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T726_ok T743_ok
def T724 : Node := Node.split 2 T725 T744
theorem T724_ok : Node.check D_R11111 T724 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T725_ok T744_ok
def T723 : Node := Node.split 1 T724 T751
theorem T723_ok : Node.check D_R11111 T723 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T724_ok T751_ok
def T722 : Node := Node.leaf L722
theorem T722_ok : Node.check D_R11111 T722 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L722_ok
def T721 : Node := Node.split 3 T722 T723
theorem T721_ok : Node.check D_R11111 T721 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T722_ok T723_ok
def T720 : Node := Node.split 0 T721 T752
theorem T720_ok : Node.check D_R11111 T720 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T721_ok T752_ok
def T719 : Node := Node.split 2 T720 T753
theorem T719_ok : Node.check D_R11111 T719 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T720_ok T753_ok
def T718 : Node := Node.leaf L718
theorem T718_ok : Node.check D_R11111 T718 [((535/512),(1605/1024)),((333/512),(999/1024)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L718_ok
def T717 : Node := Node.split 1 T718 T719
theorem T717_ok : Node.check D_R11111 T717 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T718_ok T719_ok
def T716 : Node := Node.leaf L716
theorem T716_ok : Node.check D_R11111 T716 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L716_ok
def T715 : Node := Node.split 3 T716 T717
theorem T715_ok : Node.check D_R11111 T715 [((535/512),(1605/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T716_ok T717_ok
def T714 : Node := Node.split 0 T715 T754
theorem T714_ok : Node.check D_R11111 T714 [((535/512),(535/256)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T715_ok T754_ok
def T713 : Node := Node.leaf L713
theorem T713_ok : Node.check D_R11111 T713 [((3745/2048),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L713_ok
def T712 : Node := Node.leaf L712
theorem T712_ok : Node.check D_R11111 T712 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L712_ok
def T711 : Node := Node.split 0 T712 T713
theorem T711_ok : Node.check D_R11111 T711 [((1605/1024),(535/256)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T712_ok T713_ok
def T710 : Node := Node.leaf L710
theorem T710_ok : Node.check D_R11111 T710 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L710_ok
def T709 : Node := Node.split 2 T710 T711
theorem T709_ok : Node.check D_R11111 T709 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T710_ok T711_ok
def T708 : Node := Node.leaf L708
theorem T708_ok : Node.check D_R11111 T708 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L708_ok
def T707 : Node := Node.split 1 T708 T709
theorem T707_ok : Node.check D_R11111 T707 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T708_ok T709_ok
def T706 : Node := Node.leaf L706
theorem T706_ok : Node.check D_R11111 T706 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L706_ok
def T705 : Node := Node.split 3 T706 T707
theorem T705_ok : Node.check D_R11111 T705 [((1605/1024),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T706_ok T707_ok
def T704 : Node := Node.leaf L704
theorem T704_ok : Node.check D_R11111 T704 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L704_ok
def T703 : Node := Node.leaf L703
theorem T703_ok : Node.check D_R11111 T703 [((535/512),(2675/2048)),((2331/2048),(333/256)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L703_ok
def T702 : Node := Node.leaf L702
theorem T702_ok : Node.check D_R11111 T702 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L702_ok
def T701 : Node := Node.leaf L701
theorem T701_ok : Node.check D_R11111 T701 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L701_ok
def T700 : Node := Node.leaf L700
theorem T700_ok : Node.check D_R11111 T700 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L700_ok
def T699 : Node := Node.split 0 T700 T701
theorem T699_ok : Node.check D_R11111 T699 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((7659/4096),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T700_ok T701_ok
def T698 : Node := Node.leaf L698
theorem T698_ok : Node.check D_R11111 T698 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((3663/2048),(7659/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L698_ok
def T697 : Node := Node.split 2 T698 T699
theorem T697_ok : Node.check D_R11111 T697 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T698_ok T699_ok
def T696 : Node := Node.leaf L696
theorem T696_ok : Node.check D_R11111 T696 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((7659/4096),(999/512)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L696_ok
def T695 : Node := Node.leaf L695
theorem T695_ok : Node.check D_R11111 T695 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((3663/2048),(7659/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L695_ok
def T694 : Node := Node.split 2 T695 T696
theorem T694_ok : Node.check D_R11111 T694 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T695_ok T696_ok
def T693 : Node := Node.split 1 T694 T697
theorem T693_ok : Node.check D_R11111 T693 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T694_ok T697_ok
def T692 : Node := Node.leaf L692
theorem T692_ok : Node.check D_R11111 T692 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L692_ok
def T691 : Node := Node.split 3 T692 T693
theorem T691_ok : Node.check D_R11111 T691 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T692_ok T693_ok
def T690 : Node := Node.split 0 T691 T702
theorem T690_ok : Node.check D_R11111 T690 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T691_ok T702_ok
def T689 : Node := Node.leaf L689
theorem T689_ok : Node.check D_R11111 T689 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(3663/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L689_ok
def T688 : Node := Node.split 2 T689 T690
theorem T688_ok : Node.check D_R11111 T688 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T689_ok T690_ok
def T687 : Node := Node.split 1 T688 T703
theorem T687_ok : Node.check D_R11111 T687 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T688_ok T703_ok
def T686 : Node := Node.leaf L686
theorem T686_ok : Node.check D_R11111 T686 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L686_ok
def T685 : Node := Node.split 3 T686 T687
theorem T685_ok : Node.check D_R11111 T685 [((535/512),(2675/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T686_ok T687_ok
def T684 : Node := Node.split 0 T685 T704
theorem T684_ok : Node.check D_R11111 T684 [((535/512),(1605/1024)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T685_ok T704_ok
def T683 : Node := Node.leaf L683
theorem T683_ok : Node.check D_R11111 T683 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L683_ok
def T682 : Node := Node.split 2 T683 T684
theorem T682_ok : Node.check D_R11111 T682 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T683_ok T684_ok
def T681 : Node := Node.leaf L681
theorem T681_ok : Node.check D_R11111 T681 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L681_ok
def T680 : Node := Node.split 1 T681 T682
theorem T680_ok : Node.check D_R11111 T680 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T681_ok T682_ok
def T679 : Node := Node.leaf L679
theorem T679_ok : Node.check D_R11111 T679 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L679_ok
def T678 : Node := Node.split 3 T679 T680
theorem T678_ok : Node.check D_R11111 T678 [((535/512),(1605/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T679_ok T680_ok
def T677 : Node := Node.split 0 T678 T705
theorem T677_ok : Node.check D_R11111 T677 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T678_ok T705_ok
def T676 : Node := Node.split 2 T677 T714
theorem T676_ok : Node.check D_R11111 T676 [((535/512),(535/256)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T677_ok T714_ok
def T675 : Node := Node.leaf L675
theorem T675_ok : Node.check D_R11111 T675 [((535/512),(535/256)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L675_ok
def T674 : Node := Node.split 1 T675 T676
theorem T674_ok : Node.check D_R11111 T674 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T675_ok T676_ok
def T673 : Node := Node.split 3 T674 T777
theorem T673_ok : Node.check D_R11111 T673 [((535/512),(535/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T674_ok T777_ok
def T672 : Node := Node.leaf L672
theorem T672_ok : Node.check D_R11111 T672 [((535/1024),(535/512)),((999/1024),(333/256)),((2331/1024),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L672_ok
def T671 : Node := Node.leaf L671
theorem T671_ok : Node.check D_R11111 T671 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L671_ok
def T670 : Node := Node.leaf L670
theorem T670_ok : Node.check D_R11111 T670 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L670_ok
def T669 : Node := Node.split 1 T670 T671
theorem T669_ok : Node.check D_R11111 T669 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T670_ok T671_ok
def T668 : Node := Node.leaf L668
theorem T668_ok : Node.check D_R11111 T668 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L668_ok
def T667 : Node := Node.split 3 T668 T669
theorem T667_ok : Node.check D_R11111 T667 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T668_ok T669_ok
def T666 : Node := Node.leaf L666
theorem T666_ok : Node.check D_R11111 T666 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L666_ok
def T665 : Node := Node.split 0 T666 T667
theorem T665_ok : Node.check D_R11111 T665 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T666_ok T667_ok
def T664 : Node := Node.split 2 T665 T672
theorem T664_ok : Node.check D_R11111 T664 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T665_ok T672_ok
def T663 : Node := Node.leaf L663
theorem T663_ok : Node.check D_R11111 T663 [((535/1024),(535/512)),((333/512),(999/1024)),((999/512),(333/128)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L663_ok
def T662 : Node := Node.split 1 T663 T664
theorem T662_ok : Node.check D_R11111 T662 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T663_ok T664_ok
def T661 : Node := Node.leaf L661
theorem T661_ok : Node.check D_R11111 T661 [((535/1024),(535/512)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L661_ok
def T660 : Node := Node.leaf L660
theorem T660_ok : Node.check D_R11111 T660 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L660_ok
def T659 : Node := Node.leaf L659
theorem T659_ok : Node.check D_R11111 T659 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L659_ok
def T658 : Node := Node.leaf L658
theorem T658_ok : Node.check D_R11111 T658 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L658_ok
def T657 : Node := Node.leaf L657
theorem T657_ok : Node.check D_R11111 T657 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L657_ok
def T656 : Node := Node.leaf L656
theorem T656_ok : Node.check D_R11111 T656 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L656_ok
def T655 : Node := Node.leaf L655
theorem T655_ok : Node.check D_R11111 T655 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L655_ok
def T654 : Node := Node.split 0 T655 T656
theorem T654_ok : Node.check D_R11111 T654 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T655_ok T656_ok
def T653 : Node := Node.leaf L653
theorem T653_ok : Node.check D_R11111 T653 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L653_ok
def T652 : Node := Node.leaf L652
theorem T652_ok : Node.check D_R11111 T652 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L652_ok
def T651 : Node := Node.split 3 T652 T653
theorem T651_ok : Node.check D_R11111 T651 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T652_ok T653_ok
def T650 : Node := Node.leaf L650
theorem T650_ok : Node.check D_R11111 T650 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L650_ok
def T649 : Node := Node.split 0 T650 T651
theorem T649_ok : Node.check D_R11111 T649 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T650_ok T651_ok
def T648 : Node := Node.split 2 T649 T654
theorem T648_ok : Node.check D_R11111 T648 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T649_ok T654_ok
def T647 : Node := Node.leaf L647
theorem T647_ok : Node.check D_R11111 T647 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L647_ok
def T646 : Node := Node.leaf L646
theorem T646_ok : Node.check D_R11111 T646 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L646_ok
def T645 : Node := Node.split 3 T646 T647
theorem T645_ok : Node.check D_R11111 T645 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T646_ok T647_ok
def T644 : Node := Node.leaf L644
theorem T644_ok : Node.check D_R11111 T644 [((3745/4096),(8025/8192)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L644_ok
def T643 : Node := Node.split 0 T644 T645
theorem T643_ok : Node.check D_R11111 T643 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((8325/4096),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T644_ok T645_ok
def T642 : Node := Node.leaf L642
theorem T642_ok : Node.check D_R11111 T642 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/512),(8325/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L642_ok
def T641 : Node := Node.split 2 T642 T643
theorem T641_ok : Node.check D_R11111 T641 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T642_ok T643_ok
def T640 : Node := Node.split 1 T641 T648
theorem T640_ok : Node.check D_R11111 T640 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T641_ok T648_ok
def T639 : Node := Node.split 3 T640 T657
theorem T639_ok : Node.check D_R11111 T639 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T640_ok T657_ok
def T638 : Node := Node.leaf L638
theorem T638_ok : Node.check D_R11111 T638 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L638_ok
def T637 : Node := Node.split 0 T638 T639
theorem T637_ok : Node.check D_R11111 T637 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T638_ok T639_ok
def T636 : Node := Node.split 2 T637 T658
theorem T636_ok : Node.check D_R11111 T636 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T637_ok T658_ok
def T635 : Node := Node.split 1 T636 T659
theorem T635_ok : Node.check D_R11111 T635 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T636_ok T659_ok
def T634 : Node := Node.split 3 T635 T660
theorem T634_ok : Node.check D_R11111 T634 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T635_ok T660_ok
def T633 : Node := Node.leaf L633
theorem T633_ok : Node.check D_R11111 T633 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L633_ok
def T632 : Node := Node.split 0 T633 T634
theorem T632_ok : Node.check D_R11111 T632 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T633_ok T634_ok
def T631 : Node := Node.split 2 T632 T661
theorem T631_ok : Node.check D_R11111 T631 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T632_ok T661_ok
def T630 : Node := Node.leaf L630
theorem T630_ok : Node.check D_R11111 T630 [((535/1024),(535/512)),((333/512),(999/1024)),((999/512),(333/128)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L630_ok
def T629 : Node := Node.split 1 T630 T631
theorem T629_ok : Node.check D_R11111 T629 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T630_ok T631_ok
def T628 : Node := Node.split 3 T629 T662
theorem T628_ok : Node.check D_R11111 T628 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T629_ok T662_ok
def T627 : Node := Node.leaf L627
theorem T627_ok : Node.check D_R11111 T627 [((0),(535/1024)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L627_ok
def T626 : Node := Node.split 0 T627 T628
theorem T626_ok : Node.check D_R11111 T626 [((0),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T627_ok T628_ok
def T625 : Node := Node.leaf L625
theorem T625_ok : Node.check D_R11111 T625 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L625_ok
def T624 : Node := Node.leaf L624
theorem T624_ok : Node.check D_R11111 T624 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L624_ok
def T623 : Node := Node.split 3 T624 T625
theorem T623_ok : Node.check D_R11111 T623 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T624_ok T625_ok
def T622 : Node := Node.leaf L622
theorem T622_ok : Node.check D_R11111 T622 [((535/1024),(1605/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L622_ok
def T621 : Node := Node.split 0 T622 T623
theorem T621_ok : Node.check D_R11111 T621 [((535/1024),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T622_ok T623_ok
def T620 : Node := Node.leaf L620
theorem T620_ok : Node.check D_R11111 T620 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(1665/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L620_ok
def T619 : Node := Node.split 2 T620 T621
theorem T619_ok : Node.check D_R11111 T619 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T620_ok T621_ok
def T618 : Node := Node.leaf L618
theorem T618_ok : Node.check D_R11111 T618 [((535/1024),(535/512)),((333/512),(999/1024)),((333/256),(999/512)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L618_ok
def T617 : Node := Node.split 1 T618 T619
theorem T617_ok : Node.check D_R11111 T617 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T618_ok T619_ok
def T616 : Node := Node.leaf L616
theorem T616_ok : Node.check D_R11111 T616 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L616_ok
def T615 : Node := Node.leaf L615
theorem T615_ok : Node.check D_R11111 T615 [((1605/2048),(535/512)),((2331/2048),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L615_ok
def T614 : Node := Node.leaf L614
theorem T614_ok : Node.check D_R11111 T614 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L614_ok
def T613 : Node := Node.leaf L613
theorem T613_ok : Node.check D_R11111 T613 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L613_ok
def T612 : Node := Node.leaf L612
theorem T612_ok : Node.check D_R11111 T612 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L612_ok
def T611 : Node := Node.split 1 T612 T613
theorem T611_ok : Node.check D_R11111 T611 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T612_ok T613_ok
def T610 : Node := Node.split 3 T611 T614
theorem T610_ok : Node.check D_R11111 T610 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T611_ok T614_ok
def T609 : Node := Node.leaf L609
theorem T609_ok : Node.check D_R11111 T609 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L609_ok
def T608 : Node := Node.split 0 T609 T610
theorem T608_ok : Node.check D_R11111 T608 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T609_ok T610_ok
def T607 : Node := Node.leaf L607
theorem T607_ok : Node.check D_R11111 T607 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((1665/1024),(3663/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L607_ok
def T606 : Node := Node.split 2 T607 T608
theorem T606_ok : Node.check D_R11111 T606 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T607_ok T608_ok
def T605 : Node := Node.split 1 T606 T615
theorem T605_ok : Node.check D_R11111 T605 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T606_ok T615_ok
def T604 : Node := Node.split 3 T605 T616
theorem T604_ok : Node.check D_R11111 T604 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T605_ok T616_ok
def T603 : Node := Node.leaf L603
theorem T603_ok : Node.check D_R11111 T603 [((535/1024),(1605/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L603_ok
def T602 : Node := Node.split 0 T603 T604
theorem T602_ok : Node.check D_R11111 T602 [((535/1024),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T603_ok T604_ok
def T601 : Node := Node.leaf L601
theorem T601_ok : Node.check D_R11111 T601 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L601_ok
def T600 : Node := Node.split 2 T601 T602
theorem T600_ok : Node.check D_R11111 T600 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T601_ok T602_ok
def T599 : Node := Node.leaf L599
theorem T599_ok : Node.check D_R11111 T599 [((535/1024),(535/512)),((333/512),(999/1024)),((333/256),(999/512)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L599_ok
def T598 : Node := Node.split 1 T599 T600
theorem T598_ok : Node.check D_R11111 T598 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T599_ok T600_ok
def T597 : Node := Node.split 3 T598 T617
theorem T597_ok : Node.check D_R11111 T597 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T598_ok T617_ok
def T596 : Node := Node.leaf L596
theorem T596_ok : Node.check D_R11111 T596 [((0),(535/1024)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L596_ok
def T595 : Node := Node.split 0 T596 T597
theorem T595_ok : Node.check D_R11111 T595 [((0),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T596_ok T597_ok
def T594 : Node := Node.split 2 T595 T626
theorem T594_ok : Node.check D_R11111 T594 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T595_ok T626_ok
def T593 : Node := Node.leaf L593
theorem T593_ok : Node.check D_R11111 T593 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L593_ok
def T592 : Node := Node.split 1 T593 T594
theorem T592_ok : Node.check D_R11111 T592 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T593_ok T594_ok
def T591 : Node := Node.leaf L591
theorem T591_ok : Node.check D_R11111 T591 [((535/1024),(535/512)),((999/1024),(333/256)),((2331/1024),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L591_ok
def T590 : Node := Node.leaf L590
theorem T590_ok : Node.check D_R11111 T590 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L590_ok
def T589 : Node := Node.leaf L589
theorem T589_ok : Node.check D_R11111 T589 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L589_ok
def T588 : Node := Node.leaf L588
theorem T588_ok : Node.check D_R11111 T588 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L588_ok
def T587 : Node := Node.split 1 T588 T589
theorem T587_ok : Node.check D_R11111 T587 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T588_ok T589_ok
def T586 : Node := Node.leaf L586
theorem T586_ok : Node.check D_R11111 T586 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L586_ok
def T585 : Node := Node.split 3 T586 T587
theorem T585_ok : Node.check D_R11111 T585 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T586_ok T587_ok
def T584 : Node := Node.leaf L584
theorem T584_ok : Node.check D_R11111 T584 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L584_ok
def T583 : Node := Node.split 0 T584 T585
theorem T583_ok : Node.check D_R11111 T583 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((4329/2048),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T584_ok T585_ok
def T582 : Node := Node.leaf L582
theorem T582_ok : Node.check D_R11111 T582 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L582_ok
def T581 : Node := Node.leaf L581
theorem T581_ok : Node.check D_R11111 T581 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L581_ok
def T580 : Node := Node.split 3 T581 T582
theorem T580_ok : Node.check D_R11111 T580 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T581_ok T582_ok
def T579 : Node := Node.leaf L579
theorem T579_ok : Node.check D_R11111 T579 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L579_ok
def T578 : Node := Node.split 0 T579 T580
theorem T578_ok : Node.check D_R11111 T578 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((8325/4096),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T579_ok T580_ok
def T577 : Node := Node.leaf L577
theorem T577_ok : Node.check D_R11111 T577 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/512),(8325/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L577_ok
def T576 : Node := Node.split 2 T577 T578
theorem T576_ok : Node.check D_R11111 T576 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T577_ok T578_ok
def T575 : Node := Node.leaf L575
theorem T575_ok : Node.check D_R11111 T575 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L575_ok
def T574 : Node := Node.split 1 T575 T576
theorem T574_ok : Node.check D_R11111 T574 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T575_ok T576_ok
def T573 : Node := Node.leaf L573
theorem T573_ok : Node.check D_R11111 T573 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L573_ok
def T572 : Node := Node.split 3 T573 T574
theorem T572_ok : Node.check D_R11111 T572 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T573_ok T574_ok
def T571 : Node := Node.leaf L571
theorem T571_ok : Node.check D_R11111 T571 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L571_ok
def T570 : Node := Node.split 0 T571 T572
theorem T570_ok : Node.check D_R11111 T570 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(4329/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T571_ok T572_ok
def T569 : Node := Node.split 2 T570 T583
theorem T569_ok : Node.check D_R11111 T569 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T570_ok T583_ok
def T568 : Node := Node.split 1 T569 T590
theorem T568_ok : Node.check D_R11111 T568 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T569_ok T590_ok
def T567 : Node := Node.leaf L567
theorem T567_ok : Node.check D_R11111 T567 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L567_ok
def T566 : Node := Node.split 3 T567 T568
theorem T566_ok : Node.check D_R11111 T566 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T567_ok T568_ok
def T565 : Node := Node.leaf L565
theorem T565_ok : Node.check D_R11111 T565 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L565_ok
def T564 : Node := Node.split 0 T565 T566
theorem T564_ok : Node.check D_R11111 T564 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(2331/1024)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T565_ok T566_ok
def T563 : Node := Node.split 2 T564 T591
theorem T563_ok : Node.check D_R11111 T563 [((535/1024),(535/512)),((999/1024),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T564_ok T591_ok
def T562 : Node := Node.leaf L562
theorem T562_ok : Node.check D_R11111 T562 [((535/1024),(535/512)),((333/512),(999/1024)),((999/512),(333/128)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L562_ok
def T561 : Node := Node.split 1 T562 T563
theorem T561_ok : Node.check D_R11111 T561 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T562_ok T563_ok
def T560 : Node := Node.leaf L560
theorem T560_ok : Node.check D_R11111 T560 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L560_ok
def T559 : Node := Node.split 3 T560 T561
theorem T559_ok : Node.check D_R11111 T559 [((535/1024),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T560_ok T561_ok
def T558 : Node := Node.leaf L558
theorem T558_ok : Node.check D_R11111 T558 [((0),(535/1024)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L558_ok
def T557 : Node := Node.split 0 T558 T559
theorem T557_ok : Node.check D_R11111 T557 [((0),(535/512)),((333/512),(333/256)),((999/512),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T558_ok T559_ok
def T556 : Node := Node.leaf L556
theorem T556_ok : Node.check D_R11111 T556 [((1605/2048),(535/512)),((2331/2048),(333/256)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L556_ok
def T555 : Node := Node.leaf L555
theorem T555_ok : Node.check D_R11111 T555 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L555_ok
def T554 : Node := Node.leaf L554
theorem T554_ok : Node.check D_R11111 T554 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((7659/4096),(999/512)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L554_ok
def T553 : Node := Node.leaf L553
theorem T553_ok : Node.check D_R11111 T553 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((3663/2048),(7659/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L553_ok
def T552 : Node := Node.split 2 T553 T554
theorem T552_ok : Node.check D_R11111 T552 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T553_ok T554_ok
def T551 : Node := Node.split 1 T552 T555
theorem T551_ok : Node.check D_R11111 T551 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T552_ok T555_ok
def T550 : Node := Node.leaf L550
theorem T550_ok : Node.check D_R11111 T550 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L550_ok
def T549 : Node := Node.split 3 T550 T551
theorem T549_ok : Node.check D_R11111 T549 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T550_ok T551_ok
def T548 : Node := Node.leaf L548
theorem T548_ok : Node.check D_R11111 T548 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L548_ok
def T547 : Node := Node.split 0 T548 T549
theorem T547_ok : Node.check D_R11111 T547 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((3663/2048),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T548_ok T549_ok
def T546 : Node := Node.leaf L546
theorem T546_ok : Node.check D_R11111 T546 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((1665/1024),(3663/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L546_ok
def T545 : Node := Node.split 2 T546 T547
theorem T545_ok : Node.check D_R11111 T545 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T546_ok T547_ok
def T544 : Node := Node.split 1 T545 T556
theorem T544_ok : Node.check D_R11111 T544 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T545_ok T556_ok
def T543 : Node := Node.leaf L543
theorem T543_ok : Node.check D_R11111 T543 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L543_ok
def T542 : Node := Node.split 3 T543 T544
theorem T542_ok : Node.check D_R11111 T542 [((1605/2048),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T543_ok T544_ok
def T541 : Node := Node.leaf L541
theorem T541_ok : Node.check D_R11111 T541 [((535/1024),(1605/2048)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L541_ok
def T540 : Node := Node.split 0 T541 T542
theorem T540_ok : Node.check D_R11111 T540 [((535/1024),(535/512)),((999/1024),(333/256)),((1665/1024),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T541_ok T542_ok
def T539 : Node := Node.leaf L539
theorem T539_ok : Node.check D_R11111 T539 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(1665/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L539_ok
def T538 : Node := Node.split 2 T539 T540
theorem T538_ok : Node.check D_R11111 T538 [((535/1024),(535/512)),((999/1024),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T539_ok T540_ok
def T537 : Node := Node.leaf L537
theorem T537_ok : Node.check D_R11111 T537 [((535/1024),(535/512)),((333/512),(999/1024)),((333/256),(999/512)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L537_ok
def T536 : Node := Node.split 1 T537 T538
theorem T536_ok : Node.check D_R11111 T536 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T537_ok T538_ok
def T535 : Node := Node.leaf L535
theorem T535_ok : Node.check D_R11111 T535 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L535_ok
def T534 : Node := Node.split 3 T535 T536
theorem T534_ok : Node.check D_R11111 T534 [((535/1024),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T535_ok T536_ok
def T533 : Node := Node.leaf L533
theorem T533_ok : Node.check D_R11111 T533 [((0),(535/1024)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L533_ok
def T532 : Node := Node.split 0 T533 T534
theorem T532_ok : Node.check D_R11111 T532 [((0),(535/512)),((333/512),(333/256)),((333/256),(999/512)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T533_ok T534_ok
def T531 : Node := Node.split 2 T532 T557
theorem T531_ok : Node.check D_R11111 T531 [((0),(535/512)),((333/512),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T532_ok T557_ok
def T530 : Node := Node.leaf L530
theorem T530_ok : Node.check D_R11111 T530 [((0),(535/512)),((0),(333/512)),((333/256),(333/128)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L530_ok
def T529 : Node := Node.split 1 T530 T531
theorem T529_ok : Node.check D_R11111 T529 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T530_ok T531_ok
def T528 : Node := Node.split 3 T529 T592
theorem T528_ok : Node.check D_R11111 T528 [((0),(535/512)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T529_ok T592_ok
def T527 : Node := Node.split 0 T528 T673
theorem T527_ok : Node.check D_R11111 T527 [((0),(535/256)),((0),(333/256)),((333/256),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T528_ok T673_ok
def T526 : Node := Node.leaf L526
theorem T526_ok : Node.check D_R11111 T526 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L526_ok
def T525 : Node := Node.leaf L525
theorem T525_ok : Node.check D_R11111 T525 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L525_ok
def T524 : Node := Node.leaf L524
theorem T524_ok : Node.check D_R11111 T524 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L524_ok
def T523 : Node := Node.leaf L523
theorem T523_ok : Node.check D_R11111 T523 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L523_ok
def T522 : Node := Node.leaf L522
theorem T522_ok : Node.check D_R11111 T522 [((8025/4096),(16585/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L522_ok
def T521 : Node := Node.leaf L521
theorem T521_ok : Node.check D_R11111 T521 [((8025/4096),(16585/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L521_ok
def T520 : Node := Node.split 1 T521 T522
theorem T520_ok : Node.check D_R11111 T520 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T521_ok T522_ok
def T519 : Node := Node.split 3 T520 T523
theorem T519_ok : Node.check D_R11111 T519 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T520_ok T523_ok
def T518 : Node := Node.split 0 T519 T524
theorem T518_ok : Node.check D_R11111 T518 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T519_ok T524_ok
def T517 : Node := Node.leaf L517
theorem T517_ok : Node.check D_R11111 T517 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L517_ok
def T516 : Node := Node.leaf L516
theorem T516_ok : Node.check D_R11111 T516 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L516_ok
def T515 : Node := Node.split 3 T516 T517
theorem T515_ok : Node.check D_R11111 T515 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T516_ok T517_ok
def T514 : Node := Node.leaf L514
theorem T514_ok : Node.check D_R11111 T514 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L514_ok
def T513 : Node := Node.split 0 T514 T515
theorem T513_ok : Node.check D_R11111 T513 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T514_ok T515_ok
def T512 : Node := Node.split 2 T513 T518
theorem T512_ok : Node.check D_R11111 T512 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T513_ok T518_ok
def T511 : Node := Node.leaf L511
theorem T511_ok : Node.check D_R11111 T511 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L511_ok
def T510 : Node := Node.leaf L510
theorem T510_ok : Node.check D_R11111 T510 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L510_ok
def T509 : Node := Node.split 3 T510 T511
theorem T509_ok : Node.check D_R11111 T509 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T510_ok T511_ok
def T508 : Node := Node.leaf L508
theorem T508_ok : Node.check D_R11111 T508 [((8025/4096),(16585/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L508_ok
def T507 : Node := Node.split 0 T508 T509
theorem T507_ok : Node.check D_R11111 T507 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T508_ok T509_ok
def T506 : Node := Node.leaf L506
theorem T506_ok : Node.check D_R11111 T506 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L506_ok
def T505 : Node := Node.split 2 T506 T507
theorem T505_ok : Node.check D_R11111 T505 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T506_ok T507_ok
def T504 : Node := Node.split 1 T505 T512
theorem T504_ok : Node.check D_R11111 T504 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T505_ok T512_ok
def T503 : Node := Node.leaf L503
theorem T503_ok : Node.check D_R11111 T503 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L503_ok
def T502 : Node := Node.leaf L502
theorem T502_ok : Node.check D_R11111 T502 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L502_ok
def T501 : Node := Node.split 0 T502 T503
theorem T501_ok : Node.check D_R11111 T501 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T502_ok T503_ok
def T500 : Node := Node.leaf L500
theorem T500_ok : Node.check D_R11111 T500 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L500_ok
def T499 : Node := Node.split 2 T500 T501
theorem T499_ok : Node.check D_R11111 T499 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T500_ok T501_ok
def T498 : Node := Node.leaf L498
theorem T498_ok : Node.check D_R11111 T498 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L498_ok
def T497 : Node := Node.split 1 T498 T499
theorem T497_ok : Node.check D_R11111 T497 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T498_ok T499_ok
def T496 : Node := Node.split 3 T497 T504
theorem T496_ok : Node.check D_R11111 T496 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T497_ok T504_ok
def T495 : Node := Node.leaf L495
theorem T495_ok : Node.check D_R11111 T495 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L495_ok
def T494 : Node := Node.leaf L494
theorem T494_ok : Node.check D_R11111 T494 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L494_ok
def T493 : Node := Node.split 3 T494 T495
theorem T493_ok : Node.check D_R11111 T493 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T494_ok T495_ok
def T492 : Node := Node.leaf L492
theorem T492_ok : Node.check D_R11111 T492 [((3745/2048),(15515/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L492_ok
def T491 : Node := Node.split 0 T492 T493
theorem T491_ok : Node.check D_R11111 T491 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T492_ok T493_ok
def T490 : Node := Node.leaf L490
theorem T490_ok : Node.check D_R11111 T490 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L490_ok
def T489 : Node := Node.split 2 T490 T491
theorem T489_ok : Node.check D_R11111 T489 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T490_ok T491_ok
def T488 : Node := Node.leaf L488
theorem T488_ok : Node.check D_R11111 T488 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L488_ok
def T487 : Node := Node.split 1 T488 T489
theorem T487_ok : Node.check D_R11111 T487 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T488_ok T489_ok
def T486 : Node := Node.leaf L486
theorem T486_ok : Node.check D_R11111 T486 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L486_ok
def T485 : Node := Node.leaf L485
theorem T485_ok : Node.check D_R11111 T485 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L485_ok
def T484 : Node := Node.split 1 T485 T486
theorem T484_ok : Node.check D_R11111 T484 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T485_ok T486_ok
def T483 : Node := Node.split 3 T484 T487
theorem T483_ok : Node.check D_R11111 T483 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T484_ok T487_ok
def T482 : Node := Node.split 0 T483 T496
theorem T482_ok : Node.check D_R11111 T482 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T483_ok T496_ok
def T481 : Node := Node.split 2 T482 T525
theorem T481_ok : Node.check D_R11111 T481 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T482_ok T525_ok
def T480 : Node := Node.split 1 T481 T526
theorem T480_ok : Node.check D_R11111 T480 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T481_ok T526_ok
def T479 : Node := Node.leaf L479
theorem T479_ok : Node.check D_R11111 T479 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L479_ok
def T478 : Node := Node.split 3 T479 T480
theorem T478_ok : Node.check D_R11111 T478 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T479_ok T480_ok
def T477 : Node := Node.leaf L477
theorem T477_ok : Node.check D_R11111 T477 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L477_ok
def T476 : Node := Node.split 0 T477 T478
theorem T476_ok : Node.check D_R11111 T476 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T477_ok T478_ok
def T475 : Node := Node.leaf L475
theorem T475_ok : Node.check D_R11111 T475 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L475_ok
def T474 : Node := Node.split 2 T475 T476
theorem T474_ok : Node.check D_R11111 T474 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T475_ok T476_ok
def T473 : Node := Node.leaf L473
theorem T473_ok : Node.check D_R11111 T473 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L473_ok
def T472 : Node := Node.split 1 T473 T474
theorem T472_ok : Node.check D_R11111 T472 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T473_ok T474_ok
def T471 : Node := Node.leaf L471
theorem T471_ok : Node.check D_R11111 T471 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L471_ok
def T470 : Node := Node.leaf L470
theorem T470_ok : Node.check D_R11111 T470 [((3745/2048),(535/256)),((2331/2048),(333/256)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L470_ok
def T469 : Node := Node.leaf L469
theorem T469_ok : Node.check D_R11111 T469 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L469_ok
def T468 : Node := Node.split 2 T469 T470
theorem T468_ok : Node.check D_R11111 T468 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T469_ok T470_ok
def T467 : Node := Node.leaf L467
theorem T467_ok : Node.check D_R11111 T467 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L467_ok
def T466 : Node := Node.leaf L466
theorem T466_ok : Node.check D_R11111 T466 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L466_ok
def T465 : Node := Node.leaf L465
theorem T465_ok : Node.check D_R11111 T465 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L465_ok
def T464 : Node := Node.leaf L464
theorem T464_ok : Node.check D_R11111 T464 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L464_ok
def T463 : Node := Node.leaf L463
theorem T463_ok : Node.check D_R11111 T463 [((8025/4096),(16585/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L463_ok
def T462 : Node := Node.leaf L462
theorem T462_ok : Node.check D_R11111 T462 [((8025/4096),(16585/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L462_ok
def T461 : Node := Node.split 1 T462 T463
theorem T461_ok : Node.check D_R11111 T461 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T462_ok T463_ok
def T460 : Node := Node.split 3 T461 T464
theorem T460_ok : Node.check D_R11111 T460 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T461_ok T464_ok
def T459 : Node := Node.split 0 T460 T465
theorem T459_ok : Node.check D_R11111 T459 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T460_ok T465_ok
def T458 : Node := Node.leaf L458
theorem T458_ok : Node.check D_R11111 T458 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L458_ok
def T457 : Node := Node.leaf L457
theorem T457_ok : Node.check D_R11111 T457 [((16585/8192),(535/256)),((8991/8192),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L457_ok
def T456 : Node := Node.leaf L456
theorem T456_ok : Node.check D_R11111 T456 [((16585/8192),(535/256)),((4329/4096),(8991/8192)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L456_ok
def T455 : Node := Node.split 1 T456 T457
theorem T455_ok : Node.check D_R11111 T455 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T456_ok T457_ok
def T454 : Node := Node.split 3 T455 T458
theorem T454_ok : Node.check D_R11111 T454 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T455_ok T458_ok
def T453 : Node := Node.leaf L453
theorem T453_ok : Node.check D_R11111 T453 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L453_ok
def T452 : Node := Node.leaf L452
theorem T452_ok : Node.check D_R11111 T452 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L452_ok
def T451 : Node := Node.split 3 T452 T453
theorem T451_ok : Node.check D_R11111 T451 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T452_ok T453_ok
def T450 : Node := Node.split 0 T451 T454
theorem T450_ok : Node.check D_R11111 T450 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T451_ok T454_ok
def T449 : Node := Node.split 2 T450 T459
theorem T449_ok : Node.check D_R11111 T449 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T450_ok T459_ok
def T448 : Node := Node.leaf L448
theorem T448_ok : Node.check D_R11111 T448 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L448_ok
def T447 : Node := Node.leaf L447
theorem T447_ok : Node.check D_R11111 T447 [((16585/8192),(535/256)),((8325/8192),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L447_ok
def T446 : Node := Node.leaf L446
theorem T446_ok : Node.check D_R11111 T446 [((16585/8192),(535/256)),((999/1024),(8325/8192)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L446_ok
def T445 : Node := Node.split 1 T446 T447
theorem T445_ok : Node.check D_R11111 T445 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T446_ok T447_ok
def T444 : Node := Node.split 3 T445 T448
theorem T444_ok : Node.check D_R11111 T444 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T445_ok T448_ok
def T443 : Node := Node.leaf L443
theorem T443_ok : Node.check D_R11111 T443 [((8025/4096),(16585/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L443_ok
def T442 : Node := Node.leaf L442
theorem T442_ok : Node.check D_R11111 T442 [((8025/4096),(16585/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L442_ok
def T441 : Node := Node.split 3 T442 T443
theorem T441_ok : Node.check D_R11111 T441 [((8025/4096),(16585/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T442_ok T443_ok
def T440 : Node := Node.split 0 T441 T444
theorem T440_ok : Node.check D_R11111 T440 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T441_ok T444_ok
def T439 : Node := Node.leaf L439
theorem T439_ok : Node.check D_R11111 T439 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L439_ok
def T438 : Node := Node.leaf L438
theorem T438_ok : Node.check D_R11111 T438 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L438_ok
def T437 : Node := Node.split 3 T438 T439
theorem T437_ok : Node.check D_R11111 T437 [((16585/8192),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T438_ok T439_ok
def T436 : Node := Node.leaf L436
theorem T436_ok : Node.check D_R11111 T436 [((8025/4096),(16585/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L436_ok
def T435 : Node := Node.split 0 T436 T437
theorem T435_ok : Node.check D_R11111 T435 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T436_ok T437_ok
def T434 : Node := Node.split 2 T435 T440
theorem T434_ok : Node.check D_R11111 T434 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T435_ok T440_ok
def T433 : Node := Node.split 1 T434 T449
theorem T433_ok : Node.check D_R11111 T433 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T434_ok T449_ok
def T432 : Node := Node.split 3 T433 T466
theorem T432_ok : Node.check D_R11111 T432 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T433_ok T466_ok
def T431 : Node := Node.leaf L431
theorem T431_ok : Node.check D_R11111 T431 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L431_ok
def T430 : Node := Node.leaf L430
theorem T430_ok : Node.check D_R11111 T430 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L430_ok
def T429 : Node := Node.leaf L429
theorem T429_ok : Node.check D_R11111 T429 [((15515/8192),(8025/4096)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L429_ok
def T428 : Node := Node.leaf L428
theorem T428_ok : Node.check D_R11111 T428 [((15515/8192),(8025/4096)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L428_ok
def T427 : Node := Node.split 1 T428 T429
theorem T427_ok : Node.check D_R11111 T427 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T428_ok T429_ok
def T426 : Node := Node.split 3 T427 T430
theorem T426_ok : Node.check D_R11111 T426 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T427_ok T430_ok
def T425 : Node := Node.leaf L425
theorem T425_ok : Node.check D_R11111 T425 [((3745/2048),(15515/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L425_ok
def T424 : Node := Node.split 0 T425 T426
theorem T424_ok : Node.check D_R11111 T424 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T425_ok T426_ok
def T423 : Node := Node.leaf L423
theorem T423_ok : Node.check D_R11111 T423 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L423_ok
def T422 : Node := Node.leaf L422
theorem T422_ok : Node.check D_R11111 T422 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L422_ok
def T421 : Node := Node.split 3 T422 T423
theorem T421_ok : Node.check D_R11111 T421 [((15515/8192),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T422_ok T423_ok
def T420 : Node := Node.leaf L420
theorem T420_ok : Node.check D_R11111 T420 [((3745/2048),(15515/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L420_ok
def T419 : Node := Node.split 0 T420 T421
theorem T419_ok : Node.check D_R11111 T419 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T420_ok T421_ok
def T418 : Node := Node.split 2 T419 T424
theorem T418_ok : Node.check D_R11111 T418 [((3745/2048),(8025/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T419_ok T424_ok
def T417 : Node := Node.leaf L417
theorem T417_ok : Node.check D_R11111 T417 [((15515/8192),(8025/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L417_ok
def T416 : Node := Node.leaf L416
theorem T416_ok : Node.check D_R11111 T416 [((15515/8192),(8025/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L416_ok
def T415 : Node := Node.split 3 T416 T417
theorem T415_ok : Node.check D_R11111 T415 [((15515/8192),(8025/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T416_ok T417_ok
def T414 : Node := Node.leaf L414
theorem T414_ok : Node.check D_R11111 T414 [((3745/2048),(15515/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L414_ok
def T413 : Node := Node.split 0 T414 T415
theorem T413_ok : Node.check D_R11111 T413 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T414_ok T415_ok
def T412 : Node := Node.leaf L412
theorem T412_ok : Node.check D_R11111 T412 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L412_ok
def T411 : Node := Node.split 2 T412 T413
theorem T411_ok : Node.check D_R11111 T411 [((3745/2048),(8025/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T412_ok T413_ok
def T410 : Node := Node.split 1 T411 T418
theorem T410_ok : Node.check D_R11111 T410 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T411_ok T418_ok
def T409 : Node := Node.split 3 T410 T431
theorem T409_ok : Node.check D_R11111 T409 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T410_ok T431_ok
def T408 : Node := Node.split 0 T409 T432
theorem T408_ok : Node.check D_R11111 T408 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T409_ok T432_ok
def T407 : Node := Node.split 2 T408 T467
theorem T407_ok : Node.check D_R11111 T407 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T408_ok T467_ok
def T406 : Node := Node.split 1 T407 T468
theorem T406_ok : Node.check D_R11111 T406 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T407_ok T468_ok
def T405 : Node := Node.split 3 T406 T471
theorem T405_ok : Node.check D_R11111 T405 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T406_ok T471_ok
def T404 : Node := Node.leaf L404
theorem T404_ok : Node.check D_R11111 T404 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L404_ok
def T403 : Node := Node.leaf L403
theorem T403_ok : Node.check D_R11111 T403 [((1605/1024),(3745/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L403_ok
def T402 : Node := Node.leaf L402
theorem T402_ok : Node.check D_R11111 T402 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L402_ok
def T401 : Node := Node.leaf L401
theorem T401_ok : Node.check D_R11111 T401 [((6955/4096),(3745/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L401_ok
def T400 : Node := Node.leaf L400
theorem T400_ok : Node.check D_R11111 T400 [((1605/1024),(6955/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L400_ok
def T399 : Node := Node.split 0 T400 T401
theorem T399_ok : Node.check D_R11111 T399 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T400_ok T401_ok
def T398 : Node := Node.split 2 T399 T402
theorem T398_ok : Node.check D_R11111 T398 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T399_ok T402_ok
def T397 : Node := Node.split 1 T398 T403
theorem T397_ok : Node.check D_R11111 T397 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T398_ok T403_ok
def T396 : Node := Node.split 3 T397 T404
theorem T396_ok : Node.check D_R11111 T396 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T397_ok T404_ok
def T395 : Node := Node.split 0 T396 T405
theorem T395_ok : Node.check D_R11111 T395 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T396_ok T405_ok
def T394 : Node := Node.leaf L394
theorem T394_ok : Node.check D_R11111 T394 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L394_ok
def T393 : Node := Node.split 2 T394 T395
theorem T393_ok : Node.check D_R11111 T393 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T394_ok T395_ok
def T392 : Node := Node.leaf L392
theorem T392_ok : Node.check D_R11111 T392 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L392_ok
def T391 : Node := Node.split 1 T392 T393
theorem T391_ok : Node.check D_R11111 T391 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T392_ok T393_ok
def T390 : Node := Node.split 3 T391 T472
theorem T390_ok : Node.check D_R11111 T390 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T391_ok T472_ok
def T389 : Node := Node.leaf L389
theorem T389_ok : Node.check D_R11111 T389 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L389_ok
def T388 : Node := Node.leaf L388
theorem T388_ok : Node.check D_R11111 T388 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L388_ok
def T387 : Node := Node.leaf L387
theorem T387_ok : Node.check D_R11111 T387 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L387_ok
def T386 : Node := Node.leaf L386
theorem T386_ok : Node.check D_R11111 T386 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L386_ok
def T385 : Node := Node.leaf L385
theorem T385_ok : Node.check D_R11111 T385 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L385_ok
def T384 : Node := Node.leaf L384
theorem T384_ok : Node.check D_R11111 T384 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L384_ok
def T383 : Node := Node.leaf L383
theorem T383_ok : Node.check D_R11111 T383 [((535/512),(9095/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L383_ok
def T382 : Node := Node.leaf L382
theorem T382_ok : Node.check D_R11111 T382 [((535/512),(9095/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L382_ok
def T381 : Node := Node.split 1 T382 T383
theorem T381_ok : Node.check D_R11111 T381 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T382_ok T383_ok
def T380 : Node := Node.split 3 T381 T384
theorem T380_ok : Node.check D_R11111 T380 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T381_ok T384_ok
def T379 : Node := Node.split 0 T380 T385
theorem T379_ok : Node.check D_R11111 T379 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T380_ok T385_ok
def T378 : Node := Node.leaf L378
theorem T378_ok : Node.check D_R11111 T378 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L378_ok
def T377 : Node := Node.leaf L377
theorem T377_ok : Node.check D_R11111 T377 [((535/512),(9095/8192)),((8991/8192),(2331/2048)),((999/1024),(4329/4096)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L377_ok
def T376 : Node := Node.leaf L376
theorem T376_ok : Node.check D_R11111 T376 [((535/512),(9095/8192)),((4329/4096),(8991/8192)),((999/1024),(4329/4096)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L376_ok
def T375 : Node := Node.split 1 T376 T377
theorem T375_ok : Node.check D_R11111 T375 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((16585/8192),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T376_ok T377_ok
def T374 : Node := Node.leaf L374
theorem T374_ok : Node.check D_R11111 T374 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L374_ok
def T373 : Node := Node.split 3 T374 T375
theorem T373_ok : Node.check D_R11111 T373 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T374_ok T375_ok
def T372 : Node := Node.split 0 T373 T378
theorem T372_ok : Node.check D_R11111 T372 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T373_ok T378_ok
def T371 : Node := Node.split 2 T372 T379
theorem T371_ok : Node.check D_R11111 T371 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T372_ok T379_ok
def T370 : Node := Node.leaf L370
theorem T370_ok : Node.check D_R11111 T370 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L370_ok
def T369 : Node := Node.leaf L369
theorem T369_ok : Node.check D_R11111 T369 [((535/512),(9095/8192)),((8325/8192),(4329/4096)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L369_ok
def T368 : Node := Node.leaf L368
theorem T368_ok : Node.check D_R11111 T368 [((535/512),(9095/8192)),((999/1024),(8325/8192)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L368_ok
def T367 : Node := Node.split 1 T368 T369
theorem T367_ok : Node.check D_R11111 T367 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T368_ok T369_ok
def T366 : Node := Node.leaf L366
theorem T366_ok : Node.check D_R11111 T366 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L366_ok
def T365 : Node := Node.split 3 T366 T367
theorem T365_ok : Node.check D_R11111 T365 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T366_ok T367_ok
def T364 : Node := Node.split 0 T365 T370
theorem T364_ok : Node.check D_R11111 T364 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T365_ok T370_ok
def T363 : Node := Node.leaf L363
theorem T363_ok : Node.check D_R11111 T363 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L363_ok
def T362 : Node := Node.leaf L362
theorem T362_ok : Node.check D_R11111 T362 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L362_ok
def T361 : Node := Node.split 0 T362 T363
theorem T361_ok : Node.check D_R11111 T361 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T362_ok T363_ok
def T360 : Node := Node.split 2 T361 T364
theorem T360_ok : Node.check D_R11111 T360 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T361_ok T364_ok
def T359 : Node := Node.split 1 T360 T371
theorem T359_ok : Node.check D_R11111 T359 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T360_ok T371_ok
def T358 : Node := Node.leaf L358
theorem T358_ok : Node.check D_R11111 T358 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L358_ok
def T357 : Node := Node.leaf L357
theorem T357_ok : Node.check D_R11111 T357 [((535/512),(9095/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((15515/8192),(8025/4096))] = true := Node.check_leaf_of _ _ _ L357_ok
def T356 : Node := Node.leaf L356
theorem T356_ok : Node.check D_R11111 T356 [((535/512),(9095/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((15515/8192),(8025/4096))] = true := Node.check_leaf_of _ _ _ L356_ok
def T355 : Node := Node.split 1 T356 T357
theorem T355_ok : Node.check D_R11111 T355 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((15515/8192),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T356_ok T357_ok
def T354 : Node := Node.leaf L354
theorem T354_ok : Node.check D_R11111 T354 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(15515/8192))] = true := Node.check_leaf_of _ _ _ L354_ok
def T353 : Node := Node.split 3 T354 T355
theorem T353_ok : Node.check D_R11111 T353 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T354_ok T355_ok
def T352 : Node := Node.split 0 T353 T358
theorem T352_ok : Node.check D_R11111 T352 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T353_ok T358_ok
def T351 : Node := Node.leaf L351
theorem T351_ok : Node.check D_R11111 T351 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L351_ok
def T350 : Node := Node.leaf L350
theorem T350_ok : Node.check D_R11111 T350 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L350_ok
def T349 : Node := Node.split 0 T350 T351
theorem T349_ok : Node.check D_R11111 T349 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T350_ok T351_ok
def T348 : Node := Node.split 2 T349 T352
theorem T348_ok : Node.check D_R11111 T348 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T349_ok T352_ok
def T347 : Node := Node.leaf L347
theorem T347_ok : Node.check D_R11111 T347 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L347_ok
def T346 : Node := Node.leaf L346
theorem T346_ok : Node.check D_R11111 T346 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L346_ok
def T345 : Node := Node.split 0 T346 T347
theorem T345_ok : Node.check D_R11111 T345 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T346_ok T347_ok
def T344 : Node := Node.leaf L344
theorem T344_ok : Node.check D_R11111 T344 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L344_ok
def T343 : Node := Node.split 2 T344 T345
theorem T343_ok : Node.check D_R11111 T343 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T344_ok T345_ok
def T342 : Node := Node.split 1 T343 T348
theorem T342_ok : Node.check D_R11111 T342 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T343_ok T348_ok
def T341 : Node := Node.split 3 T342 T359
theorem T341_ok : Node.check D_R11111 T341 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T342_ok T359_ok
def T340 : Node := Node.split 0 T341 T386
theorem T340_ok : Node.check D_R11111 T340 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T341_ok T386_ok
def T339 : Node := Node.split 2 T340 T387
theorem T339_ok : Node.check D_R11111 T339 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T340_ok T387_ok
def T338 : Node := Node.split 1 T339 T388
theorem T338_ok : Node.check D_R11111 T338 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T339_ok T388_ok
def T337 : Node := Node.leaf L337
theorem T337_ok : Node.check D_R11111 T337 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L337_ok
def T336 : Node := Node.leaf L336
theorem T336_ok : Node.check D_R11111 T336 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L336_ok
def T335 : Node := Node.leaf L335
theorem T335_ok : Node.check D_R11111 T335 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L335_ok
def T334 : Node := Node.leaf L334
theorem T334_ok : Node.check D_R11111 T334 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((6955/4096),(3745/2048))] = true := Node.check_leaf_of _ _ _ L334_ok
def T333 : Node := Node.leaf L333
theorem T333_ok : Node.check D_R11111 T333 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/1024),(6955/4096))] = true := Node.check_leaf_of _ _ _ L333_ok
def T332 : Node := Node.split 3 T333 T334
theorem T332_ok : Node.check D_R11111 T332 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/1024),(3745/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T333_ok T334_ok
def T331 : Node := Node.split 0 T332 T335
theorem T331_ok : Node.check D_R11111 T331 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/1024),(3745/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T332_ok T335_ok
def T330 : Node := Node.split 2 T331 T336
theorem T330_ok : Node.check D_R11111 T330 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T331_ok T336_ok
def T329 : Node := Node.split 1 T330 T337
theorem T329_ok : Node.check D_R11111 T329 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T330_ok T337_ok
def T328 : Node := Node.split 3 T329 T338
theorem T328_ok : Node.check D_R11111 T328 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T329_ok T338_ok
def T327 : Node := Node.split 0 T328 T389
theorem T327_ok : Node.check D_R11111 T327 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T328_ok T389_ok
def T326 : Node := Node.leaf L326
theorem T326_ok : Node.check D_R11111 T326 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L326_ok
def T325 : Node := Node.split 2 T326 T327
theorem T325_ok : Node.check D_R11111 T325 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T326_ok T327_ok
def T324 : Node := Node.leaf L324
theorem T324_ok : Node.check D_R11111 T324 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L324_ok
def T323 : Node := Node.split 1 T324 T325
theorem T323_ok : Node.check D_R11111 T323 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T324_ok T325_ok
def T322 : Node := Node.leaf L322
theorem T322_ok : Node.check D_R11111 T322 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L322_ok
def T321 : Node := Node.leaf L321
theorem T321_ok : Node.check D_R11111 T321 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L321_ok
def T320 : Node := Node.leaf L320
theorem T320_ok : Node.check D_R11111 T320 [((535/512),(2675/2048)),((2331/2048),(333/256)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L320_ok
def T319 : Node := Node.leaf L319
theorem T319_ok : Node.check D_R11111 T319 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L319_ok
def T318 : Node := Node.split 2 T319 T320
theorem T318_ok : Node.check D_R11111 T318 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T319_ok T320_ok
def T317 : Node := Node.leaf L317
theorem T317_ok : Node.check D_R11111 T317 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L317_ok
def T316 : Node := Node.leaf L316
theorem T316_ok : Node.check D_R11111 T316 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L316_ok
def T315 : Node := Node.leaf L315
theorem T315_ok : Node.check D_R11111 T315 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L315_ok
def T314 : Node := Node.leaf L314
theorem T314_ok : Node.check D_R11111 T314 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L314_ok
def T313 : Node := Node.leaf L313
theorem T313_ok : Node.check D_R11111 T313 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L313_ok
def T312 : Node := Node.leaf L312
theorem T312_ok : Node.check D_R11111 T312 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L312_ok
def T311 : Node := Node.leaf L311
theorem T311_ok : Node.check D_R11111 T311 [((535/512),(9095/8192)),((8991/8192),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L311_ok
def T310 : Node := Node.leaf L310
theorem T310_ok : Node.check D_R11111 T310 [((535/512),(9095/8192)),((4329/4096),(8991/8192)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L310_ok
def T309 : Node := Node.split 1 T310 T311
theorem T309_ok : Node.check D_R11111 T309 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T310_ok T311_ok
def T308 : Node := Node.split 3 T309 T312
theorem T308_ok : Node.check D_R11111 T308 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T309_ok T312_ok
def T307 : Node := Node.split 0 T308 T313
theorem T307_ok : Node.check D_R11111 T307 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T308_ok T313_ok
def T306 : Node := Node.split 2 T307 T314
theorem T306_ok : Node.check D_R11111 T306 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T307_ok T314_ok
def T305 : Node := Node.leaf L305
theorem T305_ok : Node.check D_R11111 T305 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L305_ok
def T304 : Node := Node.leaf L304
theorem T304_ok : Node.check D_R11111 T304 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L304_ok
def T303 : Node := Node.leaf L303
theorem T303_ok : Node.check D_R11111 T303 [((535/512),(9095/8192)),((8325/8192),(4329/4096)),((8991/8192),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L303_ok
def T302 : Node := Node.leaf L302
theorem T302_ok : Node.check D_R11111 T302 [((535/512),(9095/8192)),((8325/8192),(4329/4096)),((4329/4096),(8991/8192)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L302_ok
def T301 : Node := Node.split 2 T302 T303
theorem T301_ok : Node.check D_R11111 T301 [((535/512),(9095/8192)),((8325/8192),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T302_ok T303_ok
def T300 : Node := Node.leaf L300
theorem T300_ok : Node.check D_R11111 T300 [((535/512),(9095/8192)),((999/1024),(8325/8192)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L300_ok
def T299 : Node := Node.split 1 T300 T301
theorem T299_ok : Node.check D_R11111 T299 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T300_ok T301_ok
def T298 : Node := Node.split 3 T299 T304
theorem T298_ok : Node.check D_R11111 T298 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T299_ok T304_ok
def T297 : Node := Node.split 0 T298 T305
theorem T297_ok : Node.check D_R11111 T297 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T298_ok T305_ok
def T296 : Node := Node.leaf L296
theorem T296_ok : Node.check D_R11111 T296 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L296_ok
def T295 : Node := Node.leaf L295
theorem T295_ok : Node.check D_R11111 T295 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L295_ok
def T294 : Node := Node.leaf L294
theorem T294_ok : Node.check D_R11111 T294 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L294_ok
def T293 : Node := Node.split 3 T294 T295
theorem T293_ok : Node.check D_R11111 T293 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T294_ok T295_ok
def T292 : Node := Node.split 0 T293 T296
theorem T292_ok : Node.check D_R11111 T292 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T293_ok T296_ok
def T291 : Node := Node.split 2 T292 T297
theorem T291_ok : Node.check D_R11111 T291 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T292_ok T297_ok
def T290 : Node := Node.split 1 T291 T306
theorem T290_ok : Node.check D_R11111 T290 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T291_ok T306_ok
def T289 : Node := Node.split 3 T290 T315
theorem T289_ok : Node.check D_R11111 T289 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T290_ok T315_ok
def T288 : Node := Node.split 0 T289 T316
theorem T288_ok : Node.check D_R11111 T288 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T289_ok T316_ok
def T287 : Node := Node.split 2 T288 T317
theorem T287_ok : Node.check D_R11111 T287 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T288_ok T317_ok
def T286 : Node := Node.split 1 T287 T318
theorem T286_ok : Node.check D_R11111 T286 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T287_ok T318_ok
def T285 : Node := Node.split 3 T286 T321
theorem T285_ok : Node.check D_R11111 T285 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T286_ok T321_ok
def T284 : Node := Node.split 0 T285 T322
theorem T284_ok : Node.check D_R11111 T284 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T285_ok T322_ok
def T283 : Node := Node.leaf L283
theorem T283_ok : Node.check D_R11111 T283 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L283_ok
def T282 : Node := Node.split 2 T283 T284
theorem T282_ok : Node.check D_R11111 T282 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T283_ok T284_ok
def T281 : Node := Node.leaf L281
theorem T281_ok : Node.check D_R11111 T281 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L281_ok
def T280 : Node := Node.split 1 T281 T282
theorem T280_ok : Node.check D_R11111 T280 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T281_ok T282_ok
def T279 : Node := Node.split 3 T280 T323
theorem T279_ok : Node.check D_R11111 T279 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T280_ok T323_ok
def T278 : Node := Node.split 0 T279 T390
theorem T278_ok : Node.check D_R11111 T278 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T279_ok T390_ok
def T277 : Node := Node.leaf L277
theorem T277_ok : Node.check D_R11111 T277 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L277_ok
def T276 : Node := Node.split 2 T277 T278
theorem T276_ok : Node.check D_R11111 T276 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T277_ok T278_ok
def T275 : Node := Node.leaf L275
theorem T275_ok : Node.check D_R11111 T275 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L275_ok
def T274 : Node := Node.split 1 T275 T276
theorem T274_ok : Node.check D_R11111 T274 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T275_ok T276_ok
def T273 : Node := Node.leaf L273
theorem T273_ok : Node.check D_R11111 T273 [((3745/2048),(535/256)),((2331/2048),(333/256)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L273_ok
def T272 : Node := Node.leaf L272
theorem T272_ok : Node.check D_R11111 T272 [((8025/4096),(535/256)),((4995/4096),(333/256)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L272_ok
def T271 : Node := Node.leaf L271
theorem T271_ok : Node.check D_R11111 T271 [((8025/4096),(535/256)),((2331/2048),(4995/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L271_ok
def T270 : Node := Node.split 1 T271 T272
theorem T270_ok : Node.check D_R11111 T270 [((8025/4096),(535/256)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T271_ok T272_ok
def T269 : Node := Node.leaf L269
theorem T269_ok : Node.check D_R11111 T269 [((8025/4096),(535/256)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L269_ok
def T268 : Node := Node.split 3 T269 T270
theorem T268_ok : Node.check D_R11111 T268 [((8025/4096),(535/256)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T269_ok T270_ok
def T267 : Node := Node.leaf L267
theorem T267_ok : Node.check D_R11111 T267 [((3745/2048),(8025/4096)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L267_ok
def T266 : Node := Node.split 0 T267 T268
theorem T266_ok : Node.check D_R11111 T266 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T267_ok T268_ok
def T265 : Node := Node.split 2 T266 T273
theorem T265_ok : Node.check D_R11111 T265 [((3745/2048),(535/256)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T266_ok T273_ok
def T264 : Node := Node.leaf L264
theorem T264_ok : Node.check D_R11111 T264 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L264_ok
def T263 : Node := Node.leaf L263
theorem T263_ok : Node.check D_R11111 T263 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L263_ok
def T262 : Node := Node.split 1 T263 T264
theorem T262_ok : Node.check D_R11111 T262 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T263_ok T264_ok
def T261 : Node := Node.leaf L261
theorem T261_ok : Node.check D_R11111 T261 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L261_ok
def T260 : Node := Node.split 3 T261 T262
theorem T260_ok : Node.check D_R11111 T260 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T261_ok T262_ok
def T259 : Node := Node.leaf L259
theorem T259_ok : Node.check D_R11111 T259 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L259_ok
def T258 : Node := Node.leaf L258
theorem T258_ok : Node.check D_R11111 T258 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L258_ok
def T257 : Node := Node.split 3 T258 T259
theorem T257_ok : Node.check D_R11111 T257 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T258_ok T259_ok
def T256 : Node := Node.split 0 T257 T260
theorem T256_ok : Node.check D_R11111 T256 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T257_ok T260_ok
def T255 : Node := Node.leaf L255
theorem T255_ok : Node.check D_R11111 T255 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L255_ok
def T254 : Node := Node.leaf L254
theorem T254_ok : Node.check D_R11111 T254 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L254_ok
def T253 : Node := Node.split 3 T254 T255
theorem T253_ok : Node.check D_R11111 T253 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T254_ok T255_ok
def T252 : Node := Node.leaf L252
theorem T252_ok : Node.check D_R11111 T252 [((8025/4096),(16585/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L252_ok
def T251 : Node := Node.leaf L251
theorem T251_ok : Node.check D_R11111 T251 [((8025/4096),(16585/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L251_ok
def T250 : Node := Node.split 1 T251 T252
theorem T250_ok : Node.check D_R11111 T250 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T251_ok T252_ok
def T249 : Node := Node.leaf L249
theorem T249_ok : Node.check D_R11111 T249 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L249_ok
def T248 : Node := Node.split 3 T249 T250
theorem T248_ok : Node.check D_R11111 T248 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T249_ok T250_ok
def T247 : Node := Node.split 0 T248 T253
theorem T247_ok : Node.check D_R11111 T247 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T248_ok T253_ok
def T246 : Node := Node.leaf L246
theorem T246_ok : Node.check D_R11111 T246 [((16585/8192),(535/256)),((8991/8192),(2331/2048)),((999/1024),(4329/4096)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L246_ok
def T245 : Node := Node.leaf L245
theorem T245_ok : Node.check D_R11111 T245 [((16585/8192),(535/256)),((4329/4096),(8991/8192)),((999/1024),(4329/4096)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L245_ok
def T244 : Node := Node.split 1 T245 T246
theorem T244_ok : Node.check D_R11111 T244 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/8192),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T245_ok T246_ok
def T243 : Node := Node.leaf L243
theorem T243_ok : Node.check D_R11111 T243 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L243_ok
def T242 : Node := Node.split 3 T243 T244
theorem T242_ok : Node.check D_R11111 T242 [((16585/8192),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T243_ok T244_ok
def T241 : Node := Node.leaf L241
theorem T241_ok : Node.check D_R11111 T241 [((8025/4096),(16585/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L241_ok
def T240 : Node := Node.split 0 T241 T242
theorem T240_ok : Node.check D_R11111 T240 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T241_ok T242_ok
def T239 : Node := Node.split 2 T240 T247
theorem T239_ok : Node.check D_R11111 T239 [((8025/4096),(535/256)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T240_ok T247_ok
def T238 : Node := Node.leaf L238
theorem T238_ok : Node.check D_R11111 T238 [((8025/4096),(535/256)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L238_ok
def T237 : Node := Node.split 1 T238 T239
theorem T237_ok : Node.check D_R11111 T237 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T238_ok T239_ok
def T236 : Node := Node.leaf L236
theorem T236_ok : Node.check D_R11111 T236 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L236_ok
def T235 : Node := Node.split 3 T236 T237
theorem T235_ok : Node.check D_R11111 T235 [((8025/4096),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T236_ok T237_ok
def T234 : Node := Node.leaf L234
theorem T234_ok : Node.check D_R11111 T234 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L234_ok
def T233 : Node := Node.leaf L233
theorem T233_ok : Node.check D_R11111 T233 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L233_ok
def T232 : Node := Node.split 3 T233 T234
theorem T232_ok : Node.check D_R11111 T232 [((3745/2048),(8025/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T233_ok T234_ok
def T231 : Node := Node.split 0 T232 T235
theorem T231_ok : Node.check D_R11111 T231 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T232_ok T235_ok
def T230 : Node := Node.split 2 T231 T256
theorem T230_ok : Node.check D_R11111 T230 [((3745/2048),(535/256)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T231_ok T256_ok
def T229 : Node := Node.split 1 T230 T265
theorem T229_ok : Node.check D_R11111 T229 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T230_ok T265_ok
def T228 : Node := Node.leaf L228
theorem T228_ok : Node.check D_R11111 T228 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L228_ok
def T227 : Node := Node.split 3 T228 T229
theorem T227_ok : Node.check D_R11111 T227 [((3745/2048),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T228_ok T229_ok
def T226 : Node := Node.leaf L226
theorem T226_ok : Node.check D_R11111 T226 [((1605/1024),(3745/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L226_ok
def T225 : Node := Node.leaf L225
theorem T225_ok : Node.check D_R11111 T225 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L225_ok
def T224 : Node := Node.leaf L224
theorem T224_ok : Node.check D_R11111 T224 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L224_ok
def T223 : Node := Node.split 2 T224 T225
theorem T223_ok : Node.check D_R11111 T223 [((1605/1024),(3745/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T224_ok T225_ok
def T222 : Node := Node.split 1 T223 T226
theorem T222_ok : Node.check D_R11111 T222 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T223_ok T226_ok
def T221 : Node := Node.leaf L221
theorem T221_ok : Node.check D_R11111 T221 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L221_ok
def T220 : Node := Node.split 3 T221 T222
theorem T220_ok : Node.check D_R11111 T220 [((1605/1024),(3745/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T221_ok T222_ok
def T219 : Node := Node.split 0 T220 T227
theorem T219_ok : Node.check D_R11111 T219 [((1605/1024),(535/256)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T220_ok T227_ok
def T218 : Node := Node.leaf L218
theorem T218_ok : Node.check D_R11111 T218 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L218_ok
def T217 : Node := Node.split 2 T218 T219
theorem T217_ok : Node.check D_R11111 T217 [((1605/1024),(535/256)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T218_ok T219_ok
def T216 : Node := Node.leaf L216
theorem T216_ok : Node.check D_R11111 T216 [((1605/1024),(535/256)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L216_ok
def T215 : Node := Node.split 1 T216 T217
theorem T215_ok : Node.check D_R11111 T215 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T216_ok T217_ok
def T214 : Node := Node.leaf L214
theorem T214_ok : Node.check D_R11111 T214 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L214_ok
def T213 : Node := Node.split 3 T214 T215
theorem T213_ok : Node.check D_R11111 T213 [((1605/1024),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T214_ok T215_ok
def T212 : Node := Node.leaf L212
theorem T212_ok : Node.check D_R11111 T212 [((2675/2048),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L212_ok
def T211 : Node := Node.leaf L211
theorem T211_ok : Node.check D_R11111 T211 [((535/512),(2675/2048)),((2331/2048),(333/256)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L211_ok
def T210 : Node := Node.leaf L210
theorem T210_ok : Node.check D_R11111 T210 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L210_ok
def T209 : Node := Node.split 2 T210 T211
theorem T209_ok : Node.check D_R11111 T209 [((535/512),(2675/2048)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T210_ok T211_ok
def T208 : Node := Node.leaf L208
theorem T208_ok : Node.check D_R11111 T208 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L208_ok
def T207 : Node := Node.leaf L207
theorem T207_ok : Node.check D_R11111 T207 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L207_ok
def T206 : Node := Node.leaf L206
theorem T206_ok : Node.check D_R11111 T206 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L206_ok
def T205 : Node := Node.split 1 T206 T207
theorem T205_ok : Node.check D_R11111 T205 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T206_ok T207_ok
def T204 : Node := Node.leaf L204
theorem T204_ok : Node.check D_R11111 T204 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L204_ok
def T203 : Node := Node.split 3 T204 T205
theorem T203_ok : Node.check D_R11111 T203 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T204_ok T205_ok
def T202 : Node := Node.split 0 T203 T208
theorem T202_ok : Node.check D_R11111 T202 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T203_ok T208_ok
def T201 : Node := Node.leaf L201
theorem T201_ok : Node.check D_R11111 T201 [((4815/4096),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L201_ok
def T200 : Node := Node.leaf L200
theorem T200_ok : Node.check D_R11111 T200 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L200_ok
def T199 : Node := Node.leaf L199
theorem T199_ok : Node.check D_R11111 T199 [((535/512),(9095/8192)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L199_ok
def T198 : Node := Node.leaf L198
theorem T198_ok : Node.check D_R11111 T198 [((535/512),(9095/8192)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L198_ok
def T197 : Node := Node.split 1 T198 T199
theorem T197_ok : Node.check D_R11111 T197 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T198_ok T199_ok
def T196 : Node := Node.leaf L196
theorem T196_ok : Node.check D_R11111 T196 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L196_ok
def T195 : Node := Node.split 3 T196 T197
theorem T195_ok : Node.check D_R11111 T195 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T196_ok T197_ok
def T194 : Node := Node.split 0 T195 T200
theorem T194_ok : Node.check D_R11111 T194 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T195_ok T200_ok
def T193 : Node := Node.leaf L193
theorem T193_ok : Node.check D_R11111 T193 [((9095/8192),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L193_ok
def T192 : Node := Node.leaf L192
theorem T192_ok : Node.check D_R11111 T192 [((535/512),(9095/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L192_ok
def T191 : Node := Node.split 0 T192 T193
theorem T191_ok : Node.check D_R11111 T191 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T192_ok T193_ok
def T190 : Node := Node.split 2 T191 T194
theorem T190_ok : Node.check D_R11111 T190 [((535/512),(4815/4096)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T191_ok T194_ok
def T189 : Node := Node.leaf L189
theorem T189_ok : Node.check D_R11111 T189 [((9095/8192),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L189_ok
def T188 : Node := Node.leaf L188
theorem T188_ok : Node.check D_R11111 T188 [((535/512),(9095/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L188_ok
def T187 : Node := Node.split 0 T188 T189
theorem T187_ok : Node.check D_R11111 T187 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T188_ok T189_ok
def T186 : Node := Node.leaf L186
theorem T186_ok : Node.check D_R11111 T186 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L186_ok
def T185 : Node := Node.split 2 T186 T187
theorem T185_ok : Node.check D_R11111 T185 [((535/512),(4815/4096)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T186_ok T187_ok
def T184 : Node := Node.split 1 T185 T190
theorem T184_ok : Node.check D_R11111 T184 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T185_ok T190_ok
def T183 : Node := Node.leaf L183
theorem T183_ok : Node.check D_R11111 T183 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L183_ok
def T182 : Node := Node.split 3 T183 T184
theorem T182_ok : Node.check D_R11111 T182 [((535/512),(4815/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T183_ok T184_ok
def T181 : Node := Node.split 0 T182 T201
theorem T181_ok : Node.check D_R11111 T181 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T182_ok T201_ok
def T180 : Node := Node.split 2 T181 T202
theorem T180_ok : Node.check D_R11111 T180 [((535/512),(2675/2048)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T181_ok T202_ok
def T179 : Node := Node.split 1 T180 T209
theorem T179_ok : Node.check D_R11111 T179 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T180_ok T209_ok
def T178 : Node := Node.leaf L178
theorem T178_ok : Node.check D_R11111 T178 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L178_ok
def T177 : Node := Node.split 3 T178 T179
theorem T177_ok : Node.check D_R11111 T177 [((535/512),(2675/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T178_ok T179_ok
def T176 : Node := Node.split 0 T177 T212
theorem T176_ok : Node.check D_R11111 T176 [((535/512),(1605/1024)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T177_ok T212_ok
def T175 : Node := Node.leaf L175
theorem T175_ok : Node.check D_R11111 T175 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L175_ok
def T174 : Node := Node.split 2 T175 T176
theorem T174_ok : Node.check D_R11111 T174 [((535/512),(1605/1024)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T175_ok T176_ok
def T173 : Node := Node.leaf L173
theorem T173_ok : Node.check D_R11111 T173 [((535/512),(1605/1024)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L173_ok
def T172 : Node := Node.split 1 T173 T174
theorem T172_ok : Node.check D_R11111 T172 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T173_ok T174_ok
def T171 : Node := Node.leaf L171
theorem T171_ok : Node.check D_R11111 T171 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L171_ok
def T170 : Node := Node.split 3 T171 T172
theorem T170_ok : Node.check D_R11111 T170 [((535/512),(1605/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T171_ok T172_ok
def T169 : Node := Node.split 0 T170 T213
theorem T169_ok : Node.check D_R11111 T169 [((535/512),(535/256)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T170_ok T213_ok
def T168 : Node := Node.leaf L168
theorem T168_ok : Node.check D_R11111 T168 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L168_ok
def T167 : Node := Node.split 2 T168 T169
theorem T167_ok : Node.check D_R11111 T167 [((535/512),(535/256)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T168_ok T169_ok
def T166 : Node := Node.leaf L166
theorem T166_ok : Node.check D_R11111 T166 [((535/512),(535/256)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L166_ok
def T165 : Node := Node.split 1 T166 T167
theorem T165_ok : Node.check D_R11111 T165 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T166_ok T167_ok
def T164 : Node := Node.split 3 T165 T274
theorem T164_ok : Node.check D_R11111 T164 [((535/512),(535/256)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T165_ok T274_ok
def T163 : Node := Node.leaf L163
theorem T163_ok : Node.check D_R11111 T163 [((1605/2048),(535/512)),((2331/2048),(333/256)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L163_ok
def T162 : Node := Node.leaf L162
theorem T162_ok : Node.check D_R11111 T162 [((3745/4096),(535/512)),((4995/4096),(333/256)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L162_ok
def T161 : Node := Node.leaf L161
theorem T161_ok : Node.check D_R11111 T161 [((3745/4096),(535/512)),((2331/2048),(4995/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L161_ok
def T160 : Node := Node.split 1 T161 T162
theorem T160_ok : Node.check D_R11111 T160 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T161_ok T162_ok
def T159 : Node := Node.leaf L159
theorem T159_ok : Node.check D_R11111 T159 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L159_ok
def T158 : Node := Node.split 3 T159 T160
theorem T158_ok : Node.check D_R11111 T158 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T159_ok T160_ok
def T157 : Node := Node.leaf L157
theorem T157_ok : Node.check D_R11111 T157 [((1605/2048),(3745/4096)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L157_ok
def T156 : Node := Node.split 0 T157 T158
theorem T156_ok : Node.check D_R11111 T156 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T157_ok T158_ok
def T155 : Node := Node.split 2 T156 T163
theorem T155_ok : Node.check D_R11111 T155 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T156_ok T163_ok
def T154 : Node := Node.leaf L154
theorem T154_ok : Node.check D_R11111 T154 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((2331/2048),(333/256)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L154_ok
def T153 : Node := Node.leaf L153
theorem T153_ok : Node.check D_R11111 T153 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((2331/2048),(333/256)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L153_ok
def T152 : Node := Node.split 1 T153 T154
theorem T152_ok : Node.check D_R11111 T152 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T153_ok T154_ok
def T151 : Node := Node.leaf L151
theorem T151_ok : Node.check D_R11111 T151 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L151_ok
def T150 : Node := Node.split 3 T151 T152
theorem T150_ok : Node.check D_R11111 T150 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T151_ok T152_ok
def T149 : Node := Node.leaf L149
theorem T149_ok : Node.check D_R11111 T149 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L149_ok
def T148 : Node := Node.split 0 T149 T150
theorem T148_ok : Node.check D_R11111 T148 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T149_ok T150_ok
def T147 : Node := Node.leaf L147
theorem T147_ok : Node.check D_R11111 T147 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L147_ok
def T146 : Node := Node.leaf L146
theorem T146_ok : Node.check D_R11111 T146 [((8025/8192),(535/512)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L146_ok
def T145 : Node := Node.leaf L145
theorem T145_ok : Node.check D_R11111 T145 [((8025/8192),(535/512)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L145_ok
def T144 : Node := Node.split 1 T145 T146
theorem T144_ok : Node.check D_R11111 T144 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T145_ok T146_ok
def T143 : Node := Node.split 3 T144 T147
theorem T143_ok : Node.check D_R11111 T143 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T144_ok T147_ok
def T142 : Node := Node.leaf L142
theorem T142_ok : Node.check D_R11111 T142 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L142_ok
def T141 : Node := Node.split 0 T142 T143
theorem T141_ok : Node.check D_R11111 T141 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T142_ok T143_ok
def T140 : Node := Node.leaf L140
theorem T140_ok : Node.check D_R11111 T140 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L140_ok
def T139 : Node := Node.split 2 T140 T141
theorem T139_ok : Node.check D_R11111 T139 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T140_ok T141_ok
def T138 : Node := Node.leaf L138
theorem T138_ok : Node.check D_R11111 T138 [((8025/8192),(535/512)),((8325/8192),(4329/4096)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L138_ok
def T137 : Node := Node.leaf L137
theorem T137_ok : Node.check D_R11111 T137 [((8025/8192),(535/512)),((999/1024),(8325/8192)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true := Node.check_leaf_of _ _ _ L137_ok
def T136 : Node := Node.split 1 T137 T138
theorem T136_ok : Node.check D_R11111 T136 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((16585/8192),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T137_ok T138_ok
def T135 : Node := Node.leaf L135
theorem T135_ok : Node.check D_R11111 T135 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(16585/8192))] = true := Node.check_leaf_of _ _ _ L135_ok
def T134 : Node := Node.split 3 T135 T136
theorem T134_ok : Node.check D_R11111 T134 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T135_ok T136_ok
def T133 : Node := Node.leaf L133
theorem T133_ok : Node.check D_R11111 T133 [((3745/4096),(8025/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L133_ok
def T132 : Node := Node.split 0 T133 T134
theorem T132_ok : Node.check D_R11111 T132 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T133_ok T134_ok
def T131 : Node := Node.leaf L131
theorem T131_ok : Node.check D_R11111 T131 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((8025/4096),(535/256))] = true := Node.check_leaf_of _ _ _ L131_ok
def T130 : Node := Node.split 2 T131 T132
theorem T130_ok : Node.check D_R11111 T130 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T131_ok T132_ok
def T129 : Node := Node.split 1 T130 T139
theorem T129_ok : Node.check D_R11111 T129 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((8025/4096),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T130_ok T139_ok
def T128 : Node := Node.leaf L128
theorem T128_ok : Node.check D_R11111 T128 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(8025/4096))] = true := Node.check_leaf_of _ _ _ L128_ok
def T127 : Node := Node.split 3 T128 T129
theorem T127_ok : Node.check D_R11111 T127 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T128_ok T129_ok
def T126 : Node := Node.leaf L126
theorem T126_ok : Node.check D_R11111 T126 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true := Node.check_leaf_of _ _ _ L126_ok
def T125 : Node := Node.split 0 T126 T127
theorem T125_ok : Node.check D_R11111 T125 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T126_ok T127_ok
def T124 : Node := Node.split 2 T125 T148
theorem T124_ok : Node.check D_R11111 T124 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T125_ok T148_ok
def T123 : Node := Node.split 1 T124 T155
theorem T123_ok : Node.check D_R11111 T123 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((3745/2048),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T124_ok T155_ok
def T122 : Node := Node.leaf L122
theorem T122_ok : Node.check D_R11111 T122 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L122_ok
def T121 : Node := Node.leaf L121
theorem T121_ok : Node.check D_R11111 T121 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true := Node.check_leaf_of _ _ _ L121_ok
def T120 : Node := Node.split 1 T121 T122
theorem T120_ok : Node.check D_R11111 T120 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(3745/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T121_ok T122_ok
def T119 : Node := Node.split 3 T120 T123
theorem T119_ok : Node.check D_R11111 T119 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T120_ok T123_ok
def T118 : Node := Node.leaf L118
theorem T118_ok : Node.check D_R11111 T118 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L118_ok
def T117 : Node := Node.split 0 T118 T119
theorem T117_ok : Node.check D_R11111 T117 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T118_ok T119_ok
def T116 : Node := Node.leaf L116
theorem T116_ok : Node.check D_R11111 T116 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L116_ok
def T115 : Node := Node.split 2 T116 T117
theorem T115_ok : Node.check D_R11111 T115 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T116_ok T117_ok
def T114 : Node := Node.leaf L114
theorem T114_ok : Node.check D_R11111 T114 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((1605/1024),(535/256))] = true := Node.check_leaf_of _ _ _ L114_ok
def T113 : Node := Node.split 1 T114 T115
theorem T113_ok : Node.check D_R11111 T113 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((1605/1024),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T114_ok T115_ok
def T112 : Node := Node.leaf L112
theorem T112_ok : Node.check D_R11111 T112 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((2675/2048),(1605/1024))] = true := Node.check_leaf_of _ _ _ L112_ok
def T111 : Node := Node.leaf L111
theorem T111_ok : Node.check D_R11111 T111 [((1605/2048),(535/512)),((2331/2048),(333/256)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L111_ok
def T110 : Node := Node.leaf L110
theorem T110_ok : Node.check D_R11111 T110 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L110_ok
def T109 : Node := Node.leaf L109
theorem T109_ok : Node.check D_R11111 T109 [((3745/4096),(535/512)),((4995/4096),(333/256)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L109_ok
def T108 : Node := Node.leaf L108
theorem T108_ok : Node.check D_R11111 T108 [((3745/4096),(535/512)),((2331/2048),(4995/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L108_ok
def T107 : Node := Node.split 1 T108 T109
theorem T107_ok : Node.check D_R11111 T107 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T108_ok T109_ok
def T106 : Node := Node.split 3 T107 T110
theorem T106_ok : Node.check D_R11111 T106 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T107_ok T110_ok
def T105 : Node := Node.leaf L105
theorem T105_ok : Node.check D_R11111 T105 [((1605/2048),(3745/4096)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L105_ok
def T104 : Node := Node.split 0 T105 T106
theorem T104_ok : Node.check D_R11111 T104 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T105_ok T106_ok
def T103 : Node := Node.split 2 T104 T111
theorem T103_ok : Node.check D_R11111 T103 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T104_ok T111_ok
def T102 : Node := Node.leaf L102
theorem T102_ok : Node.check D_R11111 T102 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L102_ok
def T101 : Node := Node.leaf L101
theorem T101_ok : Node.check D_R11111 T101 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((4815/4096),(2675/2048))] = true := Node.check_leaf_of _ _ _ L101_ok
def T100 : Node := Node.leaf L100
theorem T100_ok : Node.check D_R11111 T100 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L100_ok
def T99 : Node := Node.leaf L99
theorem T99_ok : Node.check D_R11111 T99 [((8025/8192),(535/512)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L99_ok
def T98 : Node := Node.leaf L98
theorem T98_ok : Node.check D_R11111 T98 [((8025/8192),(535/512)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L98_ok
def T97 : Node := Node.split 1 T98 T99
theorem T97_ok : Node.check D_R11111 T97 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T98_ok T99_ok
def T96 : Node := Node.split 3 T97 T100
theorem T96_ok : Node.check D_R11111 T96 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T97_ok T100_ok
def T95 : Node := Node.leaf L95
theorem T95_ok : Node.check D_R11111 T95 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L95_ok
def T94 : Node := Node.split 0 T95 T96
theorem T94_ok : Node.check D_R11111 T94 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T95_ok T96_ok
def T93 : Node := Node.leaf L93
theorem T93_ok : Node.check D_R11111 T93 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L93_ok
def T92 : Node := Node.leaf L92
theorem T92_ok : Node.check D_R11111 T92 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L92_ok
def T91 : Node := Node.split 3 T92 T93
theorem T91_ok : Node.check D_R11111 T91 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T92_ok T93_ok
def T90 : Node := Node.leaf L90
theorem T90_ok : Node.check D_R11111 T90 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L90_ok
def T89 : Node := Node.split 0 T90 T91
theorem T89_ok : Node.check D_R11111 T89 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T90_ok T91_ok
def T88 : Node := Node.split 2 T89 T94
theorem T88_ok : Node.check D_R11111 T88 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T89_ok T94_ok
def T87 : Node := Node.leaf L87
theorem T87_ok : Node.check D_R11111 T87 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((9095/8192),(4815/4096))] = true := Node.check_leaf_of _ _ _ L87_ok
def T86 : Node := Node.leaf L86
theorem T86_ok : Node.check D_R11111 T86 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(9095/8192))] = true := Node.check_leaf_of _ _ _ L86_ok
def T85 : Node := Node.split 3 T86 T87
theorem T85_ok : Node.check D_R11111 T85 [((8025/8192),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T86_ok T87_ok
def T84 : Node := Node.leaf L84
theorem T84_ok : Node.check D_R11111 T84 [((3745/4096),(8025/8192)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L84_ok
def T83 : Node := Node.split 0 T84 T85
theorem T83_ok : Node.check D_R11111 T83 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((4329/4096),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T84_ok T85_ok
def T82 : Node := Node.leaf L82
theorem T82_ok : Node.check D_R11111 T82 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(4329/4096)),((535/512),(4815/4096))] = true := Node.check_leaf_of _ _ _ L82_ok
def T81 : Node := Node.split 2 T82 T83
theorem T81_ok : Node.check D_R11111 T81 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T82_ok T83_ok
def T80 : Node := Node.split 1 T81 T88
theorem T80_ok : Node.check D_R11111 T80 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(4815/4096))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T81_ok T88_ok
def T79 : Node := Node.split 3 T80 T101
theorem T79_ok : Node.check D_R11111 T79 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T80_ok T101_ok
def T78 : Node := Node.leaf L78
theorem T78_ok : Node.check D_R11111 T78 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true := Node.check_leaf_of _ _ _ L78_ok
def T77 : Node := Node.split 0 T78 T79
theorem T77_ok : Node.check D_R11111 T77 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T78_ok T79_ok
def T76 : Node := Node.split 2 T77 T102
theorem T76_ok : Node.check D_R11111 T76 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T77_ok T102_ok
def T75 : Node := Node.split 1 T76 T103
theorem T75_ok : Node.check D_R11111 T75 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(2675/2048))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T76_ok T103_ok
def T74 : Node := Node.split 3 T75 T112
theorem T74_ok : Node.check D_R11111 T74 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T75_ok T112_ok
def T73 : Node := Node.leaf L73
theorem T73_ok : Node.check D_R11111 T73 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L73_ok
def T72 : Node := Node.split 0 T73 T74
theorem T72_ok : Node.check D_R11111 T72 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T73_ok T74_ok
def T71 : Node := Node.leaf L71
theorem T71_ok : Node.check D_R11111 T71 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L71_ok
def T70 : Node := Node.split 2 T71 T72
theorem T70_ok : Node.check D_R11111 T70 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T71_ok T72_ok
def T69 : Node := Node.leaf L69
theorem T69_ok : Node.check D_R11111 T69 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/512),(1605/1024))] = true := Node.check_leaf_of _ _ _ L69_ok
def T68 : Node := Node.split 1 T69 T70
theorem T68_ok : Node.check D_R11111 T68 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(1605/1024))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T69_ok T70_ok
def T67 : Node := Node.split 3 T68 T113
theorem T67_ok : Node.check D_R11111 T67 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T68_ok T113_ok
def T66 : Node := Node.leaf L66
theorem T66_ok : Node.check D_R11111 T66 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L66_ok
def T65 : Node := Node.split 0 T66 T67
theorem T65_ok : Node.check D_R11111 T65 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T66_ok T67_ok
def T64 : Node := Node.leaf L64
theorem T64_ok : Node.check D_R11111 T64 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L64_ok
def T63 : Node := Node.split 2 T64 T65
theorem T63_ok : Node.check D_R11111 T63 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T64_ok T65_ok
def T62 : Node := Node.leaf L62
theorem T62_ok : Node.check D_R11111 T62 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((535/512),(535/256))] = true := Node.check_leaf_of _ _ _ L62_ok
def T61 : Node := Node.split 1 T62 T63
theorem T61_ok : Node.check D_R11111 T61 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((535/512),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T62_ok T63_ok
def T60 : Node := Node.leaf L60
theorem T60_ok : Node.check D_R11111 T60 [((1605/2048),(535/512)),((2331/2048),(333/256)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L60_ok
def T59 : Node := Node.leaf L59
theorem T59_ok : Node.check D_R11111 T59 [((3745/4096),(535/512)),((4995/4096),(333/256)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L59_ok
def T58 : Node := Node.leaf L58
theorem T58_ok : Node.check D_R11111 T58 [((3745/4096),(535/512)),((2331/2048),(4995/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L58_ok
def T57 : Node := Node.split 1 T58 T59
theorem T57_ok : Node.check D_R11111 T57 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T58_ok T59_ok
def T56 : Node := Node.leaf L56
theorem T56_ok : Node.check D_R11111 T56 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L56_ok
def T55 : Node := Node.split 3 T56 T57
theorem T55_ok : Node.check D_R11111 T55 [((3745/4096),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T56_ok T57_ok
def T54 : Node := Node.leaf L54
theorem T54_ok : Node.check D_R11111 T54 [((1605/2048),(3745/4096)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L54_ok
def T53 : Node := Node.split 0 T54 T55
theorem T53_ok : Node.check D_R11111 T53 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T54_ok T55_ok
def T52 : Node := Node.split 2 T53 T60
theorem T52_ok : Node.check D_R11111 T52 [((1605/2048),(535/512)),((2331/2048),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T53_ok T60_ok
def T51 : Node := Node.leaf L51
theorem T51_ok : Node.check D_R11111 T51 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L51_ok
def T50 : Node := Node.leaf L50
theorem T50_ok : Node.check D_R11111 T50 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((4995/4096),(333/256)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L50_ok
def T49 : Node := Node.leaf L49
theorem T49_ok : Node.check D_R11111 T49 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((2331/2048),(4995/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L49_ok
def T48 : Node := Node.split 2 T49 T50
theorem T48_ok : Node.check D_R11111 T48 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T49_ok T50_ok
def T47 : Node := Node.split 1 T48 T51
theorem T47_ok : Node.check D_R11111 T47 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T48_ok T51_ok
def T46 : Node := Node.leaf L46
theorem T46_ok : Node.check D_R11111 T46 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L46_ok
def T45 : Node := Node.split 3 T46 T47
theorem T45_ok : Node.check D_R11111 T45 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T46_ok T47_ok
def T44 : Node := Node.leaf L44
theorem T44_ok : Node.check D_R11111 T44 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L44_ok
def T43 : Node := Node.split 0 T44 T45
theorem T43_ok : Node.check D_R11111 T43 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((2331/2048),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T44_ok T45_ok
def T42 : Node := Node.leaf L42
theorem T42_ok : Node.check D_R11111 T42 [((8025/8192),(535/512)),((8991/8192),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L42_ok
def T41 : Node := Node.leaf L41
theorem T41_ok : Node.check D_R11111 T41 [((8025/8192),(535/512)),((4329/4096),(8991/8192)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true := Node.check_leaf_of _ _ _ L41_ok
def T40 : Node := Node.split 1 T41 T42
theorem T40_ok : Node.check D_R11111 T40 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((8025/8192),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T41_ok T42_ok
def T39 : Node := Node.leaf L39
theorem T39_ok : Node.check D_R11111 T39 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(8025/8192))] = true := Node.check_leaf_of _ _ _ L39_ok
def T38 : Node := Node.split 3 T39 T40
theorem T38_ok : Node.check D_R11111 T38 [((8025/8192),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T39_ok T40_ok
def T37 : Node := Node.leaf L37
theorem T37_ok : Node.check D_R11111 T37 [((3745/4096),(8025/8192)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L37_ok
def T36 : Node := Node.split 0 T37 T38
theorem T36_ok : Node.check D_R11111 T36 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((4329/4096),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T37_ok T38_ok
def T35 : Node := Node.leaf L35
theorem T35_ok : Node.check D_R11111 T35 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(4329/4096)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L35_ok
def T34 : Node := Node.split 2 T35 T36
theorem T34_ok : Node.check D_R11111 T34 [((3745/4096),(535/512)),((4329/4096),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T35_ok T36_ok
def T33 : Node := Node.leaf L33
theorem T33_ok : Node.check D_R11111 T33 [((3745/4096),(535/512)),((999/1024),(4329/4096)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true := Node.check_leaf_of _ _ _ L33_ok
def T32 : Node := Node.split 1 T33 T34
theorem T32_ok : Node.check D_R11111 T32 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((3745/4096),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T33_ok T34_ok
def T31 : Node := Node.leaf L31
theorem T31_ok : Node.check D_R11111 T31 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(3745/4096))] = true := Node.check_leaf_of _ _ _ L31_ok
def T30 : Node := Node.split 3 T31 T32
theorem T30_ok : Node.check D_R11111 T30 [((3745/4096),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T31_ok T32_ok
def T29 : Node := Node.leaf L29
theorem T29_ok : Node.check D_R11111 T29 [((1605/2048),(3745/4096)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true := Node.check_leaf_of _ _ _ L29_ok
def T28 : Node := Node.split 0 T29 T30
theorem T28_ok : Node.check D_R11111 T28 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(2331/2048)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T29_ok T30_ok
def T27 : Node := Node.split 2 T28 T43
theorem T27_ok : Node.check D_R11111 T27 [((1605/2048),(535/512)),((999/1024),(2331/2048)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T28_ok T43_ok
def T26 : Node := Node.split 1 T27 T52
theorem T26_ok : Node.check D_R11111 T26 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((1605/2048),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T27_ok T52_ok
def T25 : Node := Node.leaf L25
theorem T25_ok : Node.check D_R11111 T25 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(1605/2048))] = true := Node.check_leaf_of _ _ _ L25_ok
def T24 : Node := Node.split 3 T25 T26
theorem T24_ok : Node.check D_R11111 T24 [((1605/2048),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T25_ok T26_ok
def T23 : Node := Node.leaf L23
theorem T23_ok : Node.check D_R11111 T23 [((535/1024),(1605/2048)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L23_ok
def T22 : Node := Node.split 0 T23 T24
theorem T22_ok : Node.check D_R11111 T22 [((535/1024),(535/512)),((999/1024),(333/256)),((999/1024),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T23_ok T24_ok
def T21 : Node := Node.leaf L21
theorem T21_ok : Node.check D_R11111 T21 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(999/1024)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L21_ok
def T20 : Node := Node.split 2 T21 T22
theorem T20_ok : Node.check D_R11111 T20 [((535/1024),(535/512)),((999/1024),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T21_ok T22_ok
def T19 : Node := Node.leaf L19
theorem T19_ok : Node.check D_R11111 T19 [((535/1024),(535/512)),((333/512),(999/1024)),((333/512),(333/256)),((535/1024),(535/512))] = true := Node.check_leaf_of _ _ _ L19_ok
def T18 : Node := Node.split 1 T19 T20
theorem T18_ok : Node.check D_R11111 T18 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((535/1024),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T19_ok T20_ok
def T17 : Node := Node.leaf L17
theorem T17_ok : Node.check D_R11111 T17 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/1024))] = true := Node.check_leaf_of _ _ _ L17_ok
def T16 : Node := Node.split 3 T17 T18
theorem T16_ok : Node.check D_R11111 T16 [((535/1024),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T17_ok T18_ok
def T15 : Node := Node.leaf L15
theorem T15_ok : Node.check D_R11111 T15 [((0),(535/1024)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L15_ok
def T14 : Node := Node.split 0 T15 T16
theorem T14_ok : Node.check D_R11111 T14 [((0),(535/512)),((333/512),(333/256)),((333/512),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T15_ok T16_ok
def T13 : Node := Node.leaf L13
theorem T13_ok : Node.check D_R11111 T13 [((0),(535/512)),((333/512),(333/256)),((0),(333/512)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L13_ok
def T12 : Node := Node.split 2 T13 T14
theorem T12_ok : Node.check D_R11111 T12 [((0),(535/512)),((333/512),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T13_ok T14_ok
def T11 : Node := Node.leaf L11
theorem T11_ok : Node.check D_R11111 T11 [((0),(535/512)),((0),(333/512)),((0),(333/256)),((0),(535/512))] = true := Node.check_leaf_of _ _ _ L11_ok
def T10 : Node := Node.split 1 T11 T12
theorem T10_ok : Node.check D_R11111 T10 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((0),(535/512))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T11_ok T12_ok
def T9 : Node := Node.split 3 T10 T61
theorem T9_ok : Node.check D_R11111 T9 [((0),(535/512)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T10_ok T61_ok
def T8 : Node := Node.split 0 T9 T164
theorem T8_ok : Node.check D_R11111 T8 [((0),(535/256)),((0),(333/256)),((0),(333/256)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T9_ok T164_ok
def T7 : Node := Node.split 2 T8 T527
theorem T7_ok : Node.check D_R11111 T7 [((0),(535/256)),((0),(333/256)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T8_ok T527_ok
def T6 : Node := Node.split 1 T7 T932
theorem T6_ok : Node.check D_R11111 T6 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((0),(535/256))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T7_ok T932_ok
def T5 : Node := Node.split 3 T6 T1481
theorem T5_ok : Node.check D_R11111 T5 [((0),(535/256)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T6_ok T1481_ok
def T4 : Node := Node.split 0 T5 T1978
theorem T4_ok : Node.check D_R11111 T4 [((0),(535/128)),((0),(333/128)),((0),(333/128)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T5_ok T1978_ok
def T3 : Node := Node.split 2 T4 T2643
theorem T3_ok : Node.check D_R11111 T3 [((0),(535/128)),((0),(333/128)),((0),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T4_ok T2643_ok
def T2 : Node := Node.split 1 T3 T2850
theorem T2_ok : Node.check D_R11111 T2 [((0),(535/128)),((0),(333/64)),((0),(333/64)),((0),(535/128))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T3_ok T2850_ok
def T1 : Node := Node.split 3 T2 T3103
theorem T1_ok : Node.check D_R11111 T1 [((0),(535/128)),((0),(333/64)),((0),(333/64)),((0),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T2_ok T3103_ok
def T0 : Node := Node.split 0 T1 T3248
theorem T0_ok : Node.check D_R11111 T0 [((0),(535/64)),((0),(333/64)),((0),(333/64)),((0),(535/64))] = true :=
  Node.check_split_of _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel) T1_ok T3248_ok

end R11111
end ZetaS.CertV2

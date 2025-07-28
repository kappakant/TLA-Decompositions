---- MODULE Paxos_chunk4_IndQuickCheck ----
EXTENDS Paxos,Naturals,TLC

CONSTANT a1,a2,a3,v1,v2
VARIABLE Inv4149_val
VARIABLE Inv415_val
VARIABLE Inv4150_val
VARIABLE Inv4151_val
VARIABLE Inv4152_val
VARIABLE Inv4153_val
VARIABLE Inv4154_val
VARIABLE Inv4155_val
VARIABLE Inv4156_val
VARIABLE Inv416_val
VARIABLE Inv4160_val
VARIABLE Inv4161_val
VARIABLE Inv4163_val
VARIABLE Inv4164_val
VARIABLE Inv4166_val
VARIABLE Inv4170_val
VARIABLE Inv4171_val
VARIABLE Inv4172_val
VARIABLE Inv4173_val
VARIABLE Inv4174_val
VARIABLE Inv4175_val
VARIABLE Inv4176_val
VARIABLE Inv4177_val
VARIABLE Inv4178_val
VARIABLE Inv4179_val
VARIABLE Inv4180_val
VARIABLE Inv4181_val
VARIABLE Inv4182_val
VARIABLE Inv4183_val
VARIABLE Inv4184_val
VARIABLE Inv4185_val
VARIABLE Inv4186_val
VARIABLE Inv4187_val
VARIABLE Inv4188_val
VARIABLE Inv4189_val
VARIABLE Inv4190_val
VARIABLE Inv4191_val
VARIABLE Inv4192_val
VARIABLE Inv4193_val
VARIABLE Inv4194_val
VARIABLE Inv4195_val
VARIABLE Inv4196_val
VARIABLE Inv4197_val
VARIABLE Inv4198_val
VARIABLE Inv4199_val
VARIABLE Inv4200_val
VARIABLE Inv4201_val
VARIABLE Inv4202_val
VARIABLE Inv4203_val
VARIABLE Inv4204_val
VARIABLE Inv4205_val
VARIABLE Inv4206_val
VARIABLE Inv4207_val
VARIABLE Inv4208_val
VARIABLE Inv4209_val
VARIABLE Inv421_val
VARIABLE Inv4210_val
VARIABLE Inv4211_val
VARIABLE Inv4218_val
VARIABLE Inv4221_val
VARIABLE Inv4222_val
VARIABLE Inv4223_val
VARIABLE Inv4224_val
VARIABLE Inv4225_val
VARIABLE Inv4226_val
VARIABLE Inv4227_val
VARIABLE Inv4228_val
VARIABLE Inv4229_val
VARIABLE Inv4230_val
VARIABLE Inv4231_val
VARIABLE Inv4232_val
VARIABLE Inv4233_val
VARIABLE Inv4234_val
VARIABLE Inv4237_val
VARIABLE Inv4238_val
VARIABLE Inv4239_val
VARIABLE Inv424_val
VARIABLE Inv4240_val
VARIABLE Inv4241_val
VARIABLE Inv4244_val
VARIABLE Inv4247_val
VARIABLE Inv4249_val
VARIABLE Inv4250_val
VARIABLE Inv4251_val
VARIABLE Inv4255_val
VARIABLE Inv4270_val
VARIABLE Inv4273_val
VARIABLE Inv4275_val
VARIABLE Inv4277_val
VARIABLE Inv4278_val
VARIABLE Inv428_val
VARIABLE Inv4280_val
VARIABLE Inv4281_val
VARIABLE Inv4288_val
VARIABLE Inv4290_val
VARIABLE Inv4291_val
VARIABLE Inv4292_val
VARIABLE Inv4302_val
VARIABLE Inv4303_val
VARIABLE Inv4308_val
VARIABLE Inv4311_val
VARIABLE Inv4312_val
VARIABLE Inv4314_val
VARIABLE Inv4318_val
VARIABLE Inv4319_val
VARIABLE Inv432_val
VARIABLE Inv4321_val
VARIABLE Inv4323_val
VARIABLE Inv4324_val
VARIABLE Inv4329_val
VARIABLE Inv433_val
VARIABLE Inv4330_val
VARIABLE Inv4331_val
VARIABLE Inv4332_val
VARIABLE Inv4333_val
VARIABLE Inv434_val
VARIABLE Inv4340_val
VARIABLE Inv4343_val
VARIABLE Inv4345_val
VARIABLE Inv4346_val
VARIABLE Inv4347_val
VARIABLE Inv4348_val
VARIABLE Inv4352_val
VARIABLE Inv4353_val
VARIABLE Inv4354_val
VARIABLE Inv4357_val
VARIABLE Inv4358_val
VARIABLE Inv4359_val
VARIABLE Inv4360_val
VARIABLE Inv4361_val
VARIABLE Inv4364_val
VARIABLE Inv4366_val
VARIABLE Inv437_val
VARIABLE Inv4370_val
VARIABLE Inv4371_val
VARIABLE Inv4372_val
VARIABLE Inv4373_val
VARIABLE Inv4375_val
VARIABLE Inv4376_val
VARIABLE Inv4378_val
VARIABLE Inv4379_val
VARIABLE Inv438_val
VARIABLE Inv4380_val
VARIABLE Inv4381_val
VARIABLE Inv4382_val
VARIABLE Inv4383_val
VARIABLE Inv4384_val
VARIABLE Inv4385_val
VARIABLE Inv4386_val
VARIABLE Inv4387_val
VARIABLE Inv4388_val
VARIABLE Inv4389_val
VARIABLE Inv4390_val
VARIABLE Inv4391_val
VARIABLE Inv4392_val
VARIABLE Inv4393_val
VARIABLE Inv4394_val
VARIABLE Inv4395_val
VARIABLE Inv4396_val
VARIABLE Inv4397_val
VARIABLE Inv4398_val
VARIABLE Inv4399_val
VARIABLE Inv440_val
VARIABLE Inv4400_val
VARIABLE Inv4401_val
VARIABLE Inv4402_val
VARIABLE Inv4403_val
VARIABLE Inv4404_val
VARIABLE Inv4405_val
VARIABLE Inv4406_val
VARIABLE Inv4407_val
VARIABLE Inv4408_val
VARIABLE Inv4409_val
VARIABLE Inv4410_val
VARIABLE Inv4411_val
VARIABLE Inv4412_val
VARIABLE Inv4414_val
VARIABLE Inv4415_val
VARIABLE Inv4416_val
VARIABLE Inv4417_val
VARIABLE Inv4418_val
VARIABLE Inv4420_val
VARIABLE Inv4421_val
VARIABLE Inv4424_val
VARIABLE Inv4425_val
VARIABLE Inv4426_val
VARIABLE Inv4427_val
VARIABLE Inv4428_val
VARIABLE Inv4429_val
VARIABLE Inv4430_val
VARIABLE Inv4431_val
VARIABLE Inv4432_val
VARIABLE Inv4433_val
VARIABLE Inv4434_val
VARIABLE Inv4435_val
VARIABLE Inv4436_val
VARIABLE Inv4437_val
VARIABLE Inv4438_val
VARIABLE Inv4440_val
VARIABLE Inv4442_val
VARIABLE Inv4444_val
VARIABLE Inv4445_val
VARIABLE Inv4446_val
VARIABLE Inv4448_val
VARIABLE Inv4449_val
VARIABLE Inv445_val
VARIABLE Inv4450_val
VARIABLE Inv4451_val
VARIABLE Inv4452_val
VARIABLE Inv4453_val
VARIABLE Inv4455_val
VARIABLE Inv4456_val
VARIABLE Inv4458_val
VARIABLE Inv4463_val
VARIABLE Inv4464_val
VARIABLE Inv4465_val
VARIABLE Inv4466_val
VARIABLE Inv4467_val
VARIABLE Inv4468_val
VARIABLE Inv4469_val
VARIABLE Inv4470_val
VARIABLE Inv4471_val
VARIABLE Inv4472_val
VARIABLE Inv4473_val
VARIABLE Inv4474_val
VARIABLE Inv4475_val
VARIABLE Inv4476_val
VARIABLE Inv4477_val
VARIABLE Inv4478_val
VARIABLE Inv4479_val
VARIABLE Inv448_val
VARIABLE Inv4480_val
VARIABLE Inv4481_val
VARIABLE Inv4482_val
VARIABLE Inv4483_val
VARIABLE Inv4484_val
VARIABLE Inv4485_val
VARIABLE Inv4488_val
VARIABLE Inv4489_val
VARIABLE Inv4490_val
VARIABLE Inv4491_val
VARIABLE Inv4492_val
VARIABLE Inv4493_val
VARIABLE Inv4494_val
VARIABLE Inv4495_val
VARIABLE Inv4496_val
VARIABLE Inv4497_val
VARIABLE Inv4498_val
VARIABLE Inv4499_val
VARIABLE Inv4501_val
VARIABLE Inv4502_val
VARIABLE Inv4503_val
VARIABLE Inv4504_val
VARIABLE Inv4505_val
VARIABLE Inv4506_val
VARIABLE Inv4507_val
VARIABLE Inv4508_val
VARIABLE Inv4509_val
VARIABLE Inv4513_val
VARIABLE Inv4516_val
VARIABLE Inv4518_val
VARIABLE Inv4519_val
VARIABLE Inv4520_val
VARIABLE Inv4521_val
VARIABLE Inv4522_val
VARIABLE Inv4525_val
VARIABLE Inv4527_val
VARIABLE Inv4535_val
VARIABLE Inv4537_val
VARIABLE Inv4538_val
VARIABLE Inv4544_val
VARIABLE Inv4547_val
VARIABLE Inv4548_val
VARIABLE Inv455_val
VARIABLE Inv4551_val
VARIABLE Inv4553_val
VARIABLE Inv4559_val
VARIABLE Inv4560_val
VARIABLE Inv4561_val
VARIABLE Inv4562_val
VARIABLE Inv4567_val
VARIABLE Inv4571_val
VARIABLE Inv4572_val
VARIABLE Inv4577_val
VARIABLE Inv4579_val
VARIABLE Inv458_val
VARIABLE Inv4581_val
VARIABLE Inv4583_val
VARIABLE Inv4586_val
VARIABLE Inv4587_val
VARIABLE Inv4590_val
VARIABLE Inv4592_val
VARIABLE Inv4593_val
VARIABLE Inv4594_val
VARIABLE Inv4596_val
VARIABLE Inv4597_val
VARIABLE Inv4598_val
VARIABLE Inv46_val
VARIABLE Inv4602_val
VARIABLE Inv4604_val
VARIABLE Inv4609_val
VARIABLE Inv4610_val
VARIABLE Inv4611_val
VARIABLE Inv4619_val
VARIABLE Inv4620_val
VARIABLE Inv4625_val
VARIABLE Inv4626_val
VARIABLE Inv4627_val
VARIABLE Inv4629_val
VARIABLE Inv4631_val
VARIABLE Inv4633_val
VARIABLE Inv4634_val
VARIABLE Inv4636_val
VARIABLE Inv4638_val
VARIABLE Inv4639_val
VARIABLE Inv4641_val
VARIABLE Inv4644_val
VARIABLE Inv4645_val
VARIABLE Inv4647_val
VARIABLE Inv4648_val
VARIABLE Inv4651_val
VARIABLE Inv4652_val
VARIABLE Inv4653_val
VARIABLE Inv4655_val
VARIABLE Inv4656_val
VARIABLE Inv4657_val
VARIABLE Inv4658_val
VARIABLE Inv4659_val
VARIABLE Inv4660_val
VARIABLE Inv4661_val
VARIABLE Inv4662_val
VARIABLE Inv4663_val
VARIABLE Inv4664_val
VARIABLE Inv4665_val
VARIABLE Inv4666_val
VARIABLE Inv4667_val
VARIABLE Inv4668_val
VARIABLE Inv4669_val
VARIABLE Inv4670_val
VARIABLE Inv4671_val
VARIABLE Inv4672_val
VARIABLE Inv4673_val
VARIABLE Inv4674_val
VARIABLE Inv4675_val
VARIABLE Inv4676_val
VARIABLE Inv4677_val
VARIABLE Inv4678_val
VARIABLE Inv4679_val
VARIABLE Inv468_val
VARIABLE Inv4680_val
VARIABLE Inv4681_val
VARIABLE Inv4683_val
VARIABLE Inv4686_val
VARIABLE Inv4687_val
VARIABLE Inv4688_val
VARIABLE Inv4689_val
VARIABLE Inv4692_val
VARIABLE Inv4693_val
VARIABLE Inv4695_val
VARIABLE Inv4696_val
VARIABLE Inv4697_val
VARIABLE Inv4698_val
VARIABLE Inv4699_val
VARIABLE Inv47_val
VARIABLE Inv4702_val
VARIABLE Inv4704_val
VARIABLE Inv4705_val
VARIABLE Inv4706_val
VARIABLE Inv4707_val
VARIABLE Inv4708_val
VARIABLE Inv4709_val
VARIABLE Inv4710_val
VARIABLE Inv4711_val
VARIABLE Inv4712_val
VARIABLE Inv4713_val
VARIABLE Inv4714_val
VARIABLE Inv4715_val
VARIABLE Inv4716_val
VARIABLE Inv4717_val
VARIABLE Inv4718_val
VARIABLE Inv4719_val
VARIABLE Inv4720_val
VARIABLE Inv4721_val
VARIABLE Inv4722_val
VARIABLE Inv4723_val
VARIABLE Inv4724_val
VARIABLE Inv4725_val
VARIABLE Inv4726_val
VARIABLE Inv4728_val
VARIABLE Inv4729_val
VARIABLE Inv473_val
VARIABLE Inv4733_val
VARIABLE Inv4735_val
VARIABLE Inv4736_val
VARIABLE Inv4738_val
VARIABLE Inv4739_val
VARIABLE Inv4740_val
VARIABLE Inv4741_val
VARIABLE Inv4742_val
VARIABLE Inv4743_val
VARIABLE Inv4744_val
VARIABLE Inv4745_val
VARIABLE Inv4748_val
VARIABLE Inv4749_val
VARIABLE Inv475_val
VARIABLE Inv4751_val
VARIABLE Inv4758_val
VARIABLE Inv4759_val
VARIABLE Inv476_val
VARIABLE Inv4760_val
VARIABLE Inv4761_val
VARIABLE Inv4762_val
VARIABLE Inv4763_val
VARIABLE Inv4764_val
VARIABLE Inv4765_val
VARIABLE Inv4766_val
VARIABLE Inv4767_val
VARIABLE Inv4768_val
VARIABLE Inv4769_val
VARIABLE Inv4770_val
VARIABLE Inv4771_val
VARIABLE Inv4772_val
VARIABLE Inv4773_val
VARIABLE Inv4774_val
VARIABLE Inv4775_val
VARIABLE Inv4776_val
VARIABLE Inv4777_val
VARIABLE Inv4778_val
VARIABLE Inv4779_val
VARIABLE Inv4780_val
VARIABLE Inv4781_val
VARIABLE Inv4782_val
VARIABLE Inv4783_val
VARIABLE Inv4784_val
VARIABLE Inv4785_val
VARIABLE Inv4786_val
VARIABLE Inv4789_val
VARIABLE Inv479_val
VARIABLE Inv4790_val
VARIABLE Inv4791_val
VARIABLE Inv4792_val
VARIABLE Inv4794_val
VARIABLE Inv4796_val
VARIABLE Inv4797_val
VARIABLE Inv4798_val
VARIABLE Inv4799_val
VARIABLE Inv480_val
VARIABLE Inv4800_val
VARIABLE Inv4801_val
VARIABLE Inv4802_val
VARIABLE Inv4803_val
VARIABLE Inv4804_val
VARIABLE Inv4805_val
VARIABLE Inv4806_val
VARIABLE Inv4807_val
VARIABLE Inv4809_val
VARIABLE Inv4819_val
VARIABLE Inv482_val
VARIABLE Inv4820_val
VARIABLE Inv4821_val
VARIABLE Inv4823_val
VARIABLE Inv4827_val
VARIABLE Inv4828_val
VARIABLE Inv4831_val
VARIABLE Inv4833_val
VARIABLE Inv4837_val
VARIABLE Inv4839_val
VARIABLE Inv4840_val
VARIABLE Inv4841_val
VARIABLE Inv4842_val
VARIABLE Inv4844_val
VARIABLE Inv4847_val
VARIABLE Inv485_val
VARIABLE Inv4850_val
VARIABLE Inv4854_val
VARIABLE Inv4858_val
VARIABLE Inv4859_val
VARIABLE Inv4861_val
VARIABLE Inv4865_val
VARIABLE Inv4868_val
VARIABLE Inv4869_val
VARIABLE Inv487_val
VARIABLE Inv4872_val
VARIABLE Inv4874_val
VARIABLE Inv4875_val
VARIABLE Inv4877_val
VARIABLE Inv4879_val
VARIABLE Inv488_val
VARIABLE Inv4881_val
VARIABLE Inv4883_val
VARIABLE Inv4884_val
VARIABLE Inv4885_val
VARIABLE Inv4887_val
VARIABLE Inv4889_val
VARIABLE Inv489_val
VARIABLE Inv4890_val
VARIABLE Inv4891_val
VARIABLE Inv4892_val
VARIABLE Inv4893_val
VARIABLE Inv4894_val
VARIABLE Inv4895_val
VARIABLE Inv4896_val
VARIABLE Inv4897_val
VARIABLE Inv4898_val
VARIABLE Inv4899_val
VARIABLE Inv4901_val
VARIABLE Inv4902_val
VARIABLE Inv4903_val
VARIABLE Inv4904_val
VARIABLE Inv4905_val
VARIABLE Inv4906_val
VARIABLE Inv4910_val
VARIABLE Inv4912_val
VARIABLE Inv4914_val
VARIABLE Inv4919_val
VARIABLE Inv4922_val
VARIABLE Inv4924_val
VARIABLE Inv4925_val
VARIABLE Inv4929_val
VARIABLE Inv4933_val
VARIABLE Inv4935_val
VARIABLE Inv4937_val
VARIABLE Inv4939_val
VARIABLE Inv4940_val
VARIABLE Inv4941_val
VARIABLE Inv4942_val
VARIABLE Inv4943_val
VARIABLE Inv4945_val
VARIABLE Inv4946_val
VARIABLE Inv4949_val
VARIABLE Inv4950_val
VARIABLE Inv4951_val
VARIABLE Inv4955_val
VARIABLE Inv4956_val
VARIABLE Inv4957_val
VARIABLE Inv4958_val
VARIABLE Inv4959_val
VARIABLE Inv4960_val
VARIABLE Inv4961_val
VARIABLE Inv4962_val
VARIABLE Inv4963_val
VARIABLE Inv4964_val
VARIABLE Inv4965_val
VARIABLE Inv4966_val
VARIABLE Inv4967_val
VARIABLE Inv4968_val
VARIABLE Inv4969_val
VARIABLE Inv4970_val
VARIABLE Inv4971_val
VARIABLE Inv4972_val
VARIABLE Inv4973_val
VARIABLE Inv4974_val
VARIABLE Inv4975_val
VARIABLE Inv4976_val
VARIABLE Inv4977_val
VARIABLE Inv4978_val
VARIABLE Inv4979_val
VARIABLE Inv4980_val
VARIABLE Inv4981_val
VARIABLE Inv4982_val
VARIABLE Inv4983_val
VARIABLE Inv4984_val
VARIABLE Inv4985_val
VARIABLE Inv4986_val
VARIABLE Inv4987_val
VARIABLE Inv4988_val
VARIABLE Inv4989_val
VARIABLE Inv4990_val
VARIABLE Inv4991_val
VARIABLE Inv4992_val
VARIABLE Inv4993_val
VARIABLE Inv4994_val
VARIABLE Inv4995_val
VARIABLE Inv4998_val
VARIABLE Inv4999_val
VARIABLE Inv5_val
VARIABLE Inv500_val
VARIABLE Inv5001_val
VARIABLE Inv5002_val
VARIABLE Inv5003_val
VARIABLE Inv5007_val
VARIABLE Inv5008_val
VARIABLE Inv5009_val
VARIABLE Inv5010_val
VARIABLE Inv5011_val
VARIABLE Inv5014_val
VARIABLE Inv5015_val
VARIABLE Inv5016_val
VARIABLE Inv5017_val
VARIABLE Inv5018_val
VARIABLE Inv5019_val
VARIABLE Inv5020_val
VARIABLE Inv5021_val
VARIABLE Inv5022_val
VARIABLE Inv5023_val
VARIABLE Inv5024_val
VARIABLE Inv5025_val
VARIABLE Inv5026_val
VARIABLE Inv5027_val
VARIABLE Inv5028_val
VARIABLE Inv5029_val
VARIABLE Inv5030_val
VARIABLE Inv5031_val
VARIABLE Inv5034_val
VARIABLE Inv5035_val
VARIABLE Inv5036_val
VARIABLE Inv5037_val
VARIABLE Inv5040_val
VARIABLE Inv5041_val
VARIABLE Inv5042_val
VARIABLE Inv5043_val
VARIABLE Inv5049_val
VARIABLE Inv505_val
VARIABLE Inv5050_val
VARIABLE Inv5051_val
VARIABLE Inv5052_val
VARIABLE Inv5054_val
VARIABLE Inv5055_val
VARIABLE Inv5056_val
VARIABLE Inv5058_val
VARIABLE Inv5059_val
VARIABLE Inv506_val
VARIABLE Inv5060_val
VARIABLE Inv5061_val
VARIABLE Inv5062_val
VARIABLE Inv5063_val
VARIABLE Inv5064_val
VARIABLE Inv5065_val
VARIABLE Inv5066_val
VARIABLE Inv5067_val
VARIABLE Inv5068_val
VARIABLE Inv5069_val
VARIABLE Inv5070_val
VARIABLE Inv5071_val
VARIABLE Inv5072_val
VARIABLE Inv5073_val
VARIABLE Inv5074_val
VARIABLE Inv5075_val
VARIABLE Inv5076_val
VARIABLE Inv5077_val
VARIABLE Inv5078_val
VARIABLE Inv5079_val
VARIABLE Inv5080_val
VARIABLE Inv5081_val
VARIABLE Inv5082_val
VARIABLE Inv5083_val
VARIABLE Inv5084_val
VARIABLE Inv5085_val
VARIABLE Inv5086_val
VARIABLE Inv5087_val
VARIABLE Inv5088_val
VARIABLE Inv5089_val
VARIABLE Inv5090_val
VARIABLE Inv5091_val
VARIABLE Inv5092_val
VARIABLE Inv5093_val
VARIABLE Inv5094_val
VARIABLE Inv5095_val
VARIABLE Inv5099_val
VARIABLE Inv5101_val
VARIABLE Inv5102_val
VARIABLE Inv5103_val
VARIABLE Inv5104_val
VARIABLE Inv5105_val
VARIABLE Inv5106_val
VARIABLE Inv5107_val
VARIABLE Inv5108_val
VARIABLE Inv5109_val
VARIABLE Inv511_val
VARIABLE Inv5110_val
VARIABLE Inv5111_val
VARIABLE Inv5112_val
VARIABLE Inv5113_val
VARIABLE Inv5114_val
VARIABLE Inv5115_val
VARIABLE Inv512_val
VARIABLE Inv5122_val
VARIABLE Inv5123_val
VARIABLE Inv5124_val
VARIABLE Inv5127_val
VARIABLE Inv5128_val
VARIABLE Inv5130_val
VARIABLE Inv5135_val
VARIABLE Inv5138_val
VARIABLE Inv5139_val
VARIABLE Inv514_val
VARIABLE Inv5141_val
VARIABLE Inv5142_val
VARIABLE Inv5146_val
VARIABLE Inv515_val
VARIABLE Inv5158_val
VARIABLE Inv5159_val
VARIABLE Inv5162_val
VARIABLE Inv5163_val
VARIABLE Inv5164_val
VARIABLE Inv5165_val
VARIABLE Inv5166_val
VARIABLE Inv5167_val
VARIABLE Inv5168_val
VARIABLE Inv5173_val
VARIABLE Inv5175_val
VARIABLE Inv5176_val
VARIABLE Inv5178_val
VARIABLE Inv5180_val
VARIABLE Inv5184_val
VARIABLE Inv5188_val
VARIABLE Inv5190_val
VARIABLE Inv5191_val
VARIABLE Inv5192_val
VARIABLE Inv5193_val
VARIABLE Inv5196_val
VARIABLE Inv5197_val
VARIABLE Inv52_val
VARIABLE Inv5200_val
VARIABLE Inv5202_val
VARIABLE Inv5203_val
VARIABLE Inv5204_val
VARIABLE Inv5205_val
VARIABLE Inv5207_val
VARIABLE Inv5209_val
VARIABLE Inv5210_val
VARIABLE Inv5212_val
VARIABLE Inv5213_val
VARIABLE Inv5215_val
VARIABLE Inv5217_val
VARIABLE Inv5219_val
VARIABLE Inv522_val
VARIABLE Inv5222_val
VARIABLE Inv5225_val
VARIABLE Inv5228_val
VARIABLE Inv5229_val
VARIABLE Inv523_val
VARIABLE Inv5230_val
VARIABLE Inv5231_val
VARIABLE Inv5236_val
VARIABLE Inv5237_val
VARIABLE Inv5238_val
VARIABLE Inv5239_val
VARIABLE Inv524_val
VARIABLE Inv5241_val
VARIABLE Inv5242_val
VARIABLE Inv5243_val
VARIABLE Inv5244_val
VARIABLE Inv5245_val
VARIABLE Inv5248_val
VARIABLE Inv5249_val
VARIABLE Inv5251_val
VARIABLE Inv5254_val
VARIABLE Inv5256_val
VARIABLE Inv5257_val
VARIABLE Inv5258_val
VARIABLE Inv5259_val
VARIABLE Inv5260_val
VARIABLE Inv5261_val
VARIABLE Inv5262_val
VARIABLE Inv5263_val
VARIABLE Inv5264_val
VARIABLE Inv5265_val
VARIABLE Inv5266_val
VARIABLE Inv5267_val
VARIABLE Inv5268_val
VARIABLE Inv5269_val
VARIABLE Inv5270_val
VARIABLE Inv5271_val
VARIABLE Inv5272_val
VARIABLE Inv5273_val
VARIABLE Inv5274_val
VARIABLE Inv5275_val
VARIABLE Inv5276_val
VARIABLE Inv5277_val
VARIABLE Inv5278_val
VARIABLE Inv5279_val
VARIABLE Inv5280_val
VARIABLE Inv5281_val
VARIABLE Inv5282_val
VARIABLE Inv5283_val
VARIABLE Inv5284_val
VARIABLE Inv5285_val
VARIABLE Inv5286_val
VARIABLE Inv5287_val
VARIABLE Inv5288_val
VARIABLE Inv5289_val
VARIABLE Inv5290_val
VARIABLE Inv5291_val
VARIABLE Inv5292_val
VARIABLE Inv5293_val
VARIABLE Inv5294_val
VARIABLE Inv5295_val
VARIABLE Inv5296_val
VARIABLE Inv5297_val
VARIABLE Inv5298_val
VARIABLE Inv5299_val
VARIABLE Inv530_val
VARIABLE Inv5300_val
VARIABLE Inv5304_val
VARIABLE Inv5305_val
VARIABLE Inv5306_val
VARIABLE Inv5308_val
VARIABLE Inv5312_val
VARIABLE Inv5313_val
VARIABLE Inv5314_val
VARIABLE Inv5315_val
VARIABLE Inv5316_val
VARIABLE Inv5317_val
VARIABLE Inv5318_val
VARIABLE Inv5319_val
VARIABLE Inv5320_val
VARIABLE Inv5321_val
VARIABLE Inv5322_val
VARIABLE Inv5323_val
VARIABLE Inv5324_val
VARIABLE Inv5325_val
VARIABLE Inv5326_val
VARIABLE Inv5327_val
VARIABLE Inv5328_val
VARIABLE Inv5329_val
VARIABLE Inv5330_val
VARIABLE Inv5331_val
VARIABLE Inv5332_val
VARIABLE Inv5333_val
VARIABLE Inv5334_val
VARIABLE Inv5336_val
VARIABLE Inv5338_val
VARIABLE Inv5339_val
VARIABLE Inv5341_val
VARIABLE Inv5343_val
VARIABLE Inv5344_val
VARIABLE Inv5346_val
VARIABLE Inv5347_val
VARIABLE Inv5349_val
VARIABLE Inv5350_val
VARIABLE Inv5351_val
VARIABLE Inv5352_val
VARIABLE Inv5353_val
VARIABLE Inv5354_val
VARIABLE Inv5355_val
VARIABLE Inv5356_val
VARIABLE Inv5357_val
VARIABLE Inv5358_val
VARIABLE Inv5359_val
VARIABLE Inv536_val
VARIABLE Inv5360_val
VARIABLE Inv5361_val
VARIABLE Inv5362_val
VARIABLE Inv5363_val
VARIABLE Inv5364_val
VARIABLE Inv5365_val
VARIABLE Inv5366_val
VARIABLE Inv5367_val
VARIABLE Inv5368_val
VARIABLE Inv5369_val
VARIABLE Inv537_val
VARIABLE Inv5370_val
VARIABLE Inv5371_val
VARIABLE Inv5372_val
VARIABLE Inv5373_val
VARIABLE Inv5374_val
VARIABLE Inv5375_val
VARIABLE Inv5376_val
VARIABLE Inv5377_val
VARIABLE Inv5378_val
VARIABLE Inv5379_val
VARIABLE Inv5381_val
VARIABLE Inv5383_val
VARIABLE Inv5384_val
VARIABLE Inv5386_val
VARIABLE Inv5387_val
VARIABLE Inv5388_val
VARIABLE Inv5389_val
VARIABLE Inv5390_val
VARIABLE Inv5391_val
VARIABLE Inv5392_val
VARIABLE Inv5393_val
VARIABLE Inv5394_val
VARIABLE Inv5395_val
VARIABLE Inv5396_val
VARIABLE Inv5397_val
VARIABLE Inv540_val
VARIABLE Inv5402_val
VARIABLE Inv5404_val
VARIABLE Inv5405_val
VARIABLE Inv541_val
VARIABLE Inv5415_val
VARIABLE Inv5416_val
VARIABLE Inv542_val
VARIABLE Inv5422_val
VARIABLE Inv5423_val
VARIABLE Inv5428_val
VARIABLE Inv5433_val
VARIABLE Inv5434_val
VARIABLE Inv5435_val
VARIABLE Inv5437_val
VARIABLE Inv5438_val
VARIABLE Inv5440_val
VARIABLE Inv5442_val
VARIABLE Inv5443_val
VARIABLE Inv5444_val
VARIABLE Inv5447_val
VARIABLE Inv5448_val
VARIABLE Inv5452_val
VARIABLE Inv5454_val
VARIABLE Inv5456_val
VARIABLE Inv5457_val
VARIABLE Inv5458_val
VARIABLE Inv5459_val
VARIABLE Inv5460_val
VARIABLE Inv5461_val
VARIABLE Inv5470_val
VARIABLE Inv5475_val
VARIABLE Inv5479_val
VARIABLE Inv548_val
VARIABLE Inv5480_val
VARIABLE Inv5481_val
VARIABLE Inv5482_val
VARIABLE Inv5483_val
VARIABLE Inv5486_val
VARIABLE Inv549_val
VARIABLE Inv5494_val
VARIABLE Inv5498_val
VARIABLE Inv5499_val
VARIABLE Inv550_val
VARIABLE Inv5501_val
VARIABLE Inv5504_val
VARIABLE Inv5506_val
VARIABLE Inv5507_val
VARIABLE Inv5508_val
VARIABLE Inv5511_val
VARIABLE Inv5512_val
VARIABLE Inv5520_val
VARIABLE Inv5521_val
VARIABLE Inv5522_val
VARIABLE Inv5523_val
VARIABLE Inv5524_val
VARIABLE Inv5525_val
VARIABLE Inv5526_val
VARIABLE Inv5527_val
VARIABLE Inv5528_val
VARIABLE Inv5529_val
VARIABLE Inv5530_val
VARIABLE Inv5531_val
VARIABLE Inv5532_val
VARIABLE Inv5533_val
VARIABLE Inv5534_val
VARIABLE Inv5535_val
VARIABLE Inv5536_val
VARIABLE Inv5537_val
VARIABLE Inv5538_val
VARIABLE Inv5539_val
VARIABLE Inv554_val
VARIABLE Inv5540_val
VARIABLE Inv5541_val
VARIABLE Inv5542_val
VARIABLE Inv5543_val
VARIABLE Inv5544_val
VARIABLE Inv5545_val
VARIABLE Inv5546_val
VARIABLE Inv5549_val
VARIABLE Inv5551_val
VARIABLE Inv5552_val
VARIABLE Inv5553_val
VARIABLE Inv5554_val
VARIABLE Inv5556_val
VARIABLE Inv5557_val
VARIABLE Inv5558_val
VARIABLE Inv556_val
VARIABLE Inv5560_val
VARIABLE Inv5562_val
VARIABLE Inv5563_val
VARIABLE Inv5564_val
VARIABLE Inv5565_val
VARIABLE Inv5566_val
VARIABLE Inv5567_val
VARIABLE Inv5568_val
VARIABLE Inv5569_val
VARIABLE Inv5570_val
VARIABLE Inv5571_val
VARIABLE Inv5572_val
VARIABLE Inv5573_val
VARIABLE Inv5574_val
VARIABLE Inv5575_val
VARIABLE Inv5577_val
VARIABLE Inv558_val
VARIABLE Inv5580_val
VARIABLE Inv5582_val
VARIABLE Inv5583_val
VARIABLE Inv5584_val
VARIABLE Inv5591_val
VARIABLE Inv5592_val
VARIABLE Inv5594_val
VARIABLE Inv5595_val
VARIABLE Inv5596_val
VARIABLE Inv5597_val
VARIABLE Inv5598_val
VARIABLE Inv5599_val
VARIABLE Inv56_val
VARIABLE Inv5600_val
VARIABLE Inv5601_val
VARIABLE Inv5602_val
VARIABLE Inv5603_val
VARIABLE Inv5604_val
VARIABLE ctiId

Inv4612_1_0 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2b(ACCI,BALJ,VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv1170_1_1 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALI)) \/ (~(msg2a(BALI,VALI)))
Inv4101_1_2 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2a(BALI,VALI)) \/ (~(ChosenAt(BALI, VALI)))
Inv5926_1_3 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : ~(maxBal[ACCI] < BALI) \/ (~(maxVBal[ACCI] = BALI))
Inv4154_1_0 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2a(BALI,VALI)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv2501_1_1 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (\E m \in msgs : m.bal >= maxBal[ACCI]) \/ ((maxBal[ACCI] = -1))
Inv6101_1_2 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : ~(maxVBal[ACCI] = -1) \/ (~(maxVal[ACCI] = VALI))
Inv6114_1_3 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : ~(maxVBal[ACCI] = -1) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv12388_2_4 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (msg2b(ACCI,BALJ,VALI)) \/ (~(maxVBal[ACCI] = BALJ) \/ (~(msg2a(BALJ,VALI))))
Inv4149 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg2a(BALI,VALI))))
Inv415 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((ChosenAt(maxBal[ACCI], VALI)) \/ (~(ChosenAt(BALI, VALJ))))
Inv4150 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((SafeAt(BALK, VALI)))
Inv4151 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((maxBal[ACCI] < BALK))
Inv4152 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((msg2a(BALJ,VALI)))
Inv4153 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv4154 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((maxVBal[ACCI] > BALJ))
Inv4155 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4156 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((maxVBal[ACCI] = BALJ))
Inv416 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((ChosenAt(maxBal[ACCI], VALI)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4160 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4161 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxBal[ACCI] < BALI) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv4163 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxBal[ACCI] < BALJ) \/ (~(maxBal[ACCI] < maxVBal[ACCI])))
Inv4164 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxBal[ACCI] < BALK) \/ (~(maxBal[ACCI] = BALK)))
Inv4166 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxBal[ACCI] = -1)) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv4170 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = -1) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4171 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(SafeAt(BALJ, VALJ)))
Inv4172 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv4173 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ ((msg2a(BALJ,VALJ)))
Inv4174 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(ChosenAt(BALK, VALI)))
Inv4175 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(SafeAt(BALK, VALI)))
Inv4176 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4177 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ ((maxVBal[ACCI] = -1))
Inv4178 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ ((maxVBal[ACCI] = BALI))
Inv4179 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4180 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(msg1a(ACCI,BALJ)))
Inv4181 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ ((maxBal[ACCI] < BALI))
Inv4182 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4183 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ (~(SafeAt(BALI, VALI)))
Inv4184 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(maxVal[ACCI] = VALI))
Inv4185 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4186 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ ((VALI = None /\ maxBal = maxBal))
Inv4187 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv4188 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(SafeAt(BALK, VALI)))
Inv4189 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(SafeAt(BALK, VALJ)))
Inv4190 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv4191 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(maxBal[ACCI] = -1))
Inv4192 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((SafeAt(BALJ, VALI)))
Inv4193 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((msg1b(ACCI,BALJ,BALK,VALI)))
Inv4194 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4195 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2a(BALK,VALJ)))
Inv4196 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4197 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((maxVBal[ACCI] = -1))
Inv4198 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4199 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv4200 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ ((msg2a(BALJ,VALI)))
Inv4201 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ (~(ChosenAt(BALK, VALI)))
Inv4202 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((VALI=VALJ /\ maxBal = maxBal))
Inv4203 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((maxBal[ACCI] = BALJ))
Inv4204 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ (~(maxVBal[ACCI] > BALI))
Inv4205 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALI))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv4206 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALI))) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4207 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(ChosenAt(BALI, VALI)))
Inv4208 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(ChosenAt(BALK, VALJ)))
Inv4209 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv421 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((ChosenAt(maxVBal[ACCI], VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv4210 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(msg2a(BALI,VALI)))
Inv4211 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4218 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2a(BALK,VALJ))) \/ ((maxVBal[ACCI] = -1))
Inv4221 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((msg2b(ACCI,BALI,VALJ)))
Inv4222 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ (~(maxVBal[ACCI] > BALI))
Inv4223 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ (~(msg1a(ACCI,BALI)))
Inv4224 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4225 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ ((msg2a(BALJ,VALJ)))
Inv4226 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ ((msg2b(ACCI,BALI,VALI)))
Inv4227 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(SafeAt(BALJ, VALJ)))
Inv4228 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(msg2a(BALK,VALI)))
Inv4229 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ ((msg2a(BALK,VALJ)))
Inv4230 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ (~(ChosenAt(BALI, VALI)))
Inv4231 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((SafeAt(BALJ, VALI)))
Inv4232 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4233 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ (~(maxBal[ACCI] = BALI))
Inv4234 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)))
Inv4237 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv4238 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALJ, VALI))))
Inv4239 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv424 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALI, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))))
Inv4240 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALK))))
Inv4241 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4244 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((SafeAt(BALK, VALJ))) \/ ((maxVBal[ACCI] = -1))
Inv4247 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VALI = None /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALI))))
Inv4249 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VALI=VALJ /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALI))))
Inv4250 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VALI=VALJ /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4251 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv4255 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALI,VALI)) \/ ((maxVBal[ACCI] = -1)))
Inv4270 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(maxVBal[ACCI] = BALI))
Inv4273 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALJ,VALJ)) \/ (~(msg1a(ACCI,BALJ))))
Inv4275 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALJ,VALJ))) \/ (~(maxVBal[ACCI] > BALJ))
Inv4277 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALK,VALI)) \/ (~(VotedFor(ACCI,BALK,VALJ))))
Inv4278 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALK,VALJ)) \/ ((maxVBal[ACCI] = -1)))
Inv428 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALI, VALI))) \/ (~(maxVal[ACCI] = VALI))
Inv4280 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((VotedFor(ACCI,BALK,VALJ))) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4281 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4288 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] < BALI) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4290 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] < BALI)) \/ (~(maxVBal[ACCI] > BALJ))
Inv4291 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] < BALJ) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4292 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] < BALK) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4302 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] = BALI) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv4303 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] = BALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv4308 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxBal[ACCI] = BALK) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv4311 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] = -1) \/ ((maxVBal[ACCI] = BALI)))
Inv4312 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ (~(msg2a(BALK,VALI)))
Inv4314 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] = BALI) \/ (~(SafeAt(BALJ, VALJ))))
Inv4318 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] > BALI) \/ (~(ChosenAt(BALI, VALJ))))
Inv4319 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] > BALI) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv432 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALI, VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4321 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVBal[ACCI] > BALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv4323 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVal[ACCI] = VALI)) \/ (~(ChosenAt(BALK, VALJ)))
Inv4324 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((maxVal[ACCI] = VALI)) \/ (~(msg2a(BALJ,VALJ)))
Inv4329 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1a(ACCI,BALK))) \/ (~(ChosenAt(BALI, VALJ)))
Inv433 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv4330 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])))
Inv4331 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv4332 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4333 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(maxVBal[ACCI] = BALI))
Inv434 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4340 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv4343 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALI,VALI)) \/ (~(msg2a(BALJ,VALI))))
Inv4345 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALI,VALI))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4346 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALI,VALJ)) \/ (~(ChosenAt(BALI, VALI))))
Inv4347 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALI,VALJ)) \/ (~(maxVal[ACCI] = VALI)))
Inv4348 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALI,VALJ)) \/ (~(msg2a(BALJ,VALI))))
Inv4352 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALJ,VALJ))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4353 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALJ,VALJ))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4354 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2a(BALK,VALI)) \/ (~(ChosenAt(BALJ, VALJ))))
Inv4357 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALI))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4358 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALI))) \/ (~(SafeAt(BALJ, VALJ)))
Inv4359 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv4360 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(msg2a(BALJ,VALI))))
Inv4361 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4364 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALI,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4366 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALJ,VALJ)) \/ (~(SafeAt(BALJ, VALJ))))
Inv437 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4370 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALJ,VALJ))) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv4371 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALK,VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv4372 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALK,VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv4373 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALK,VALJ)) \/ (~(msg1a(ACCI,BALK))))
Inv4375 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALK,VALJ))) \/ (~(maxVBal[ACCI] = BALI))
Inv4376 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ ((msg2b(ACCI,BALK,VALJ))) \/ (~(msg2a(BALJ,VALI)))
Inv4378 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI))))
Inv4379 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(maxBal[ACCI] = BALJ)))
Inv438 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4380 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4381 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv4382 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ ((maxBal[ACCI] < BALJ))
Inv4383 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ (~(VotedFor(ACCI,BALI,VALJ)))
Inv4384 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI)))
Inv4385 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((maxBal[ACCI] = -1))
Inv4386 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((maxVBal[ACCI] = BALI))
Inv4387 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(maxBal[ACCI] = BALK))
Inv4388 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALI))) \/ ((VotedFor(ACCI,BALJ,VALJ)))
Inv4389 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(SafeAt(BALJ, VALJ)))
Inv4390 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv4391 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(ChosenAt(BALK, VALI))))
Inv4392 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALJ))))
Inv4393 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(msg2a(BALI,VALJ))))
Inv4394 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALJ))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv4395 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALI, VALJ))) \/ (~(maxVBal[ACCI] = BALJ))
Inv4396 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < BALK)))
Inv4397 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALI))) \/ ((msg1b(ACCI,BALJ,BALK,VALI)))
Inv4398 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)))
Inv4399 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv440 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALJ))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4400 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((msg2b(ACCI,BALI,VALI)))
Inv4401 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALJ))) \/ (~(msg2a(BALI,VALJ)))
Inv4402 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv4403 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALI))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv4404 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALI))) \/ ((msg1a(ACCI,BALJ)))
Inv4405 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv4406 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(msg2a(BALJ,VALI))))
Inv4407 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALK, VALJ))) \/ ((msg2b(ACCI,BALJ,VALJ)))
Inv4408 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(SafeAt(BALJ, VALJ))))
Inv4409 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(msg1a(ACCI,BALJ))))
Inv4410 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4411 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv4412 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ (~(SafeAt(BALJ, VALJ)))
Inv4414 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(SafeAt(BALI, VALJ)) \/ (~(msg1a(ACCI,BALI))))
Inv4415 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(SafeAt(BALI, VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4416 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(SafeAt(BALJ, VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4417 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(SafeAt(BALK, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4418 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4420 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VALI = None /\ maxBal = maxBal) \/ (~(VALI=VALJ /\ maxBal = maxBal)))
Inv4421 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ ((msg1a(ACCI,BALJ)))
Inv4424 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VALI=VALJ /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = BALI))
Inv4425 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI)))
Inv4426 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4427 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((msg2a(BALJ,VALI)))
Inv4428 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ (~(maxVBal[ACCI] = BALJ))
Inv4429 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI)) \/ (~(maxBal[ACCI] < BALI)))
Inv4430 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI)) \/ (~(maxVal[ACCI] = VALI)))
Inv4431 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((VALJ = None /\ maxBal = maxBal))
Inv4432 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(SafeAt(BALI, VALJ)))
Inv4433 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(maxBal[ACCI] = BALK)))
Inv4434 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv4435 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv4436 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv4437 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((msg1a(ACCI,BALI)))
Inv4438 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(maxVBal[ACCI] > BALJ)))
Inv4440 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4442 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(maxVBal[ACCI] > BALI)))
Inv4444 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4445 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < BALI)) \/ (~(maxVal[ACCI] = VALI))
Inv4446 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < BALJ) \/ (~(msg1a(ACCI,BALK))))
Inv4448 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < BALJ)) \/ (~(maxBal[ACCI] = BALJ))
Inv4449 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ ((msg1b(ACCI,BALJ,BALK,VALI)))
Inv445 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALK, VALJ))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4450 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4451 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = -1) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv4452 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = -1)) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4453 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = -1)) \/ (~(msg2a(BALJ,VALI)))
Inv4455 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = BALI)) \/ (~(ChosenAt(BALK, VALI)))
Inv4456 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = BALJ)) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv4458 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = BALK)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4463 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] = -1)) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv4464 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4465 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] = BALJ)) \/ ((maxBal[ACCI] = -1))
Inv4466 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4467 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(maxBal[ACCI] = BALJ))
Inv4468 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] > BALI) \/ (~(maxVal[ACCI] = VALI)))
Inv4469 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(SafeAt(BALI, VALJ)))
Inv4470 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4471 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] > BALJ)) \/ ((msg2a(BALI,VALJ)))
Inv4472 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(msg2a(BALI,VALI)))
Inv4473 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVal[ACCI] = VALI)) \/ ((VALI = None /\ maxBal = maxBal))
Inv4474 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(maxVal[ACCI] = VALI)) \/ ((maxVBal[ACCI] > BALI))
Inv4475 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv4476 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ ((maxVBal[ACCI] = BALI))
Inv4477 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(maxVBal[ACCI] = BALJ))
Inv4478 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1a(ACCI,BALK))) \/ (~(maxVBal[ACCI] = BALI))
Inv4479 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((maxBal[ACCI] = BALK))
Inv448 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALK, VALJ))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4480 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((maxVBal[ACCI] = -1))
Inv4481 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(maxBal[ACCI] < BALK))
Inv4482 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4483 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv4484 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((VALJ = None /\ maxBal = maxBal))
Inv4485 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4488 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALI,VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4489 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALI,VALJ))) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv4490 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALI))) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv4491 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALI))) \/ ((maxVal[ACCI] = VALI))
Inv4492 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALI))) \/ ((msg2b(ACCI,BALJ,VALJ)))
Inv4493 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALI))) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv4494 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALI))) \/ (~(maxVBal[ACCI] = -1))
Inv4495 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4496 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALJ,VALJ))) \/ (~(maxBal[ACCI] < BALI))
Inv4497 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4498 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4499 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv4501 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2a(BALK,VALJ))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv4502 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((SafeAt(BALK, VALI)))
Inv4503 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ (~(msg2a(BALK,VALI)))
Inv4504 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ ((VotedFor(ACCI,BALI,VALI)))
Inv4505 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ ((maxBal[ACCI] < maxVBal[ACCI]))
Inv4506 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4507 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4508 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv4509 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ (~(maxBal[ACCI] = BALJ))
Inv4513 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv4516 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((SafeAt(BALK, VALJ))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv4518 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VALI=VALJ /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv4519 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VALI=VALJ /\ maxBal = maxBal) \/ (~(ChosenAt(maxBal[ACCI], VALI))))
Inv4520 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(SafeAt(BALJ, VALI))))
Inv4521 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal)) \/ ((maxVBal[ACCI] = -1))
Inv4522 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4525 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALI,VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)))
Inv4527 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALI,VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4535 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv4537 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal)))
Inv4538 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI))))
Inv4544 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALK,VALI)) \/ (~(msg2a(BALJ,VALI))))
Inv4547 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALK,VALJ)) \/ (~(ChosenAt(BALJ, VALJ))))
Inv4548 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((VotedFor(ACCI,BALK,VALJ)) \/ (~(SafeAt(BALJ, VALI))))
Inv455 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VALI=VALJ /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALK))))
Inv4551 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4553 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(VotedFor(ACCI,BALI,VALJ)))
Inv4559 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] < BALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4560 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] < BALI)) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv4561 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] < BALJ) \/ (~(BALJ = -1 /\ maxBal = maxBal)))
Inv4562 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] < BALJ) \/ (~(ChosenAt(BALI, VALJ))))
Inv4567 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] = -1) \/ (~(maxBal[ACCI] < maxVBal[ACCI])))
Inv4571 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] = BALI)) \/ (~(msg1a(ACCI,BALK)))
Inv4572 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] = BALI)) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4577 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxBal[ACCI] = BALK)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv4579 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] = -1) \/ ((msg2b(ACCI,BALI,VALI))))
Inv458 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI)))
Inv4581 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] = BALI) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4583 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] = BALI)) \/ (~(ChosenAt(BALI, VALI)))
Inv4586 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] = BALJ)) \/ (~(maxVBal[ACCI] > BALI))
Inv4587 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] > BALI)) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv4590 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] > BALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4592 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVBal[ACCI] > BALJ)) \/ (~(maxVBal[ACCI] > BALI))
Inv4593 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVal[ACCI] = VALI) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv4594 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVal[ACCI] = VALI) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv4596 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVal[ACCI] = VALI)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4597 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((maxVal[ACCI] = VALI)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv4598 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1a(ACCI,BALI)) \/ (~(maxVBal[ACCI] > BALI)))
Inv46 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALI = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALI, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv4602 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1a(ACCI,BALI))) \/ (~(maxVBal[ACCI] = BALJ))
Inv4604 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1a(ACCI,BALJ))) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv4609 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1a(ACCI,BALK))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv4610 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4611 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4619 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1b(ACCI,BALJ,BALK,VALI))) \/ (~(maxVBal[ACCI] = BALI))
Inv4620 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv4625 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALI,VALJ))) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv4626 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALJ,VALI)) \/ (~(ChosenAt(BALK, VALJ))))
Inv4627 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALJ,VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4629 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALJ,VALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv4631 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALJ,VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv4633 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALJ,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4634 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALK,VALI)) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv4636 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALK,VALJ)) \/ (~(ChosenAt(BALI, VALJ))))
Inv4638 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2a(BALK,VALJ))) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv4639 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALI,VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv4641 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALI,VALI))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4644 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALI,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4645 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI)) \/ (~(msg1a(ACCI,BALJ))))
Inv4647 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI))) \/ (~(msg2a(BALJ,VALI)))
Inv4648 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4651 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALK,VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4652 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALK,VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv4653 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALK,VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4655 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ ((msg2b(ACCI,BALK,VALJ))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4656 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALJ))))
Inv4657 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv4658 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] > BALI))
Inv4659 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4660 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = BALJ))
Inv4661 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(SafeAt(BALI, VALJ))))
Inv4662 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))))
Inv4663 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(SafeAt(BALK, VALI)))
Inv4664 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = BALI))
Inv4665 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] > BALJ))
Inv4666 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALI))) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv4667 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALI))) \/ ((maxBal[ACCI] = BALK))
Inv4668 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))))
Inv4669 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4670 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(msg2a(BALJ,VALI))))
Inv4671 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALJ))) \/ ((maxVBal[ACCI] = BALJ))
Inv4672 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALI, VALJ))) \/ (~(maxBal[ACCI] < BALJ))
Inv4673 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALJ, VALI)) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv4674 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALJ, VALI))) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv4675 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((maxBal[ACCI] = BALJ))
Inv4676 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(BALK, VALI))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4677 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv4678 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4679 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(maxVal[ACCI] = VALI))
Inv468 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALJ,VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)))
Inv4680 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))))
Inv4681 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv4683 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4686 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALJ, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv4687 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALJ, VALI))) \/ ((maxVBal[ACCI] = BALJ))
Inv4688 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALJ, VALI))) \/ ((msg2a(BALK,VALI)))
Inv4689 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALK, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4692 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALK, VALJ)) \/ (~(msg2a(BALJ,VALI))))
Inv4693 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4695 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(SafeAt(BALK, VALJ))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4696 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALI = None /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < BALI)))
Inv4697 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4698 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALI=VALJ /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4699 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALI=VALJ /\ maxBal = maxBal) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv47 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALI = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALI, VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4702 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALI=VALJ /\ maxBal = maxBal)) \/ (~(msg1a(ACCI,BALI)))
Inv4704 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ (~(msg1a(ACCI,BALK)))
Inv4705 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv4706 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((VotedFor(ACCI,BALK,VALJ)))
Inv4707 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((maxBal[ACCI] < BALK))
Inv4708 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((maxVBal[ACCI] = -1))
Inv4709 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv4710 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv4711 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4712 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv4713 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv4714 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI)) \/ (~(maxVBal[ACCI] = -1)))
Inv4715 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((VotedFor(ACCI,BALI,VALI)))
Inv4716 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ (~(msg2a(BALJ,VALJ)))
Inv4717 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ)) \/ (~(msg2a(BALI,VALI))))
Inv4718 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ ((maxVBal[ACCI] > BALJ))
Inv4719 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4720 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(SafeAt(BALK, VALI)))
Inv4721 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4722 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4723 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((msg2a(BALI,VALI)))
Inv4724 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4725 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4726 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4728 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(msg2a(BALJ,VALI))))
Inv4729 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(SafeAt(BALJ, VALI)))
Inv473 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI))))
Inv4733 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < BALJ) \/ (~(maxVBal[ACCI] > BALJ)))
Inv4735 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < BALJ)) \/ (~(ChosenAt(BALK, VALI)))
Inv4736 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < BALJ)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4738 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv4739 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv4740 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4741 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4742 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = -1) \/ (~(maxBal[ACCI] = BALK)))
Inv4743 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = -1)) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv4744 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = -1)) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv4745 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = BALI) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv4748 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = BALI)) \/ (~(ChosenAt(BALK, VALI)))
Inv4749 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = BALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv475 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALI))) \/ (~(maxVal[ACCI] = VALI))
Inv4751 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxBal[ACCI] = BALJ) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4758 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ ((maxVBal[ACCI] > BALI))
Inv4759 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ ((maxVBal[ACCI] > BALJ))
Inv476 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALI))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4760 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ ((msg1b(ACCI,BALJ,BALK,VALI)))
Inv4761 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ ((msg2b(ACCI,BALI,VALI)))
Inv4762 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4763 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(ChosenAt(BALJ, VALI)))
Inv4764 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(maxBal[ACCI] < BALI))
Inv4765 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4766 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv4767 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4768 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ ((msg2a(BALK,VALI)))
Inv4769 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ (~(ChosenAt(BALI, VALJ)))
Inv4770 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ (~(maxVBal[ACCI] = -1))
Inv4771 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4772 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4773 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ (~(msg2a(BALJ,VALJ)))
Inv4774 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4775 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALK)) \/ (~(msg2a(BALI,VALI))))
Inv4776 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALK)) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4777 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ ((VALI=VALJ /\ maxBal = maxBal))
Inv4778 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ ((msg2a(BALK,VALI)))
Inv4779 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(ChosenAt(BALK, VALJ)))
Inv4780 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv4781 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv4782 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((msg2a(BALK,VALI)))
Inv4783 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ ((VotedFor(ACCI,BALK,VALJ)))
Inv4784 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv4785 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALI,VALI))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4786 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALI,VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv4789 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALJ,VALI))) \/ (~(msg1a(ACCI,BALJ)))
Inv479 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALJ))) \/ ((maxVBal[ACCI] = -1))
Inv4790 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALJ,VALJ))) \/ ((msg1a(ACCI,BALK)))
Inv4791 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALJ,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv4792 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALJ,VALJ))) \/ (~(maxBal[ACCI] = BALJ))
Inv4794 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALK,VALI))) \/ (~(maxBal[ACCI] = BALJ))
Inv4796 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2a(BALK,VALJ))) \/ (~(msg1a(ACCI,BALJ)))
Inv4797 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4798 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((maxBal[ACCI] = -1))
Inv4799 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((maxVBal[ACCI] = BALI))
Inv480 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALJ))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4800 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ ((msg2b(ACCI,BALI,VALI)))
Inv4801 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ (~(SafeAt(BALK, VALJ)))
Inv4802 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(msg2a(BALI,VALJ)))
Inv4803 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(msg2a(BALK,VALJ)))
Inv4804 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv4805 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ (~(maxVBal[ACCI] > BALI))
Inv4806 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((SafeAt(BALK, VALI)))
Inv4807 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4809 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv4819 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VALI=VALJ /\ maxBal = maxBal)) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv482 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(msg1a(ACCI,BALK))))
Inv4820 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4821 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VALJ = None /\ maxBal = maxBal)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv4823 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALI,VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4827 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALI,VALI))) \/ (~(maxVBal[ACCI] > BALI))
Inv4828 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALI,VALI))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4831 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(ChosenAt(BALJ, VALI)))
Inv4833 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(msg1a(ACCI,BALJ)))
Inv4837 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALJ,VALJ))) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv4839 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALK,VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])))
Inv4840 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALK,VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4841 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALK,VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal)))
Inv4842 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALK,VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4844 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((VotedFor(ACCI,BALK,VALJ))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv4847 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv485 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv4850 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv4854 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv4858 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALJ) \/ (~(maxVBal[ACCI] > BALJ)))
Inv4859 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALJ) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv4861 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv4865 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALK) \/ (~(maxVBal[ACCI] = BALI)))
Inv4868 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALK)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4869 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < BALK)) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv487 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ ((maxBal[ACCI] < BALJ))
Inv4872 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] < maxVBal[ACCI])) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4874 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = -1) \/ (~(maxVBal[ACCI] = BALI)))
Inv4875 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = -1) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv4877 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = -1)) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv4879 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = -1)) \/ (~(msg2a(BALK,VALI)))
Inv488 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4881 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALI) \/ (~(maxVBal[ACCI] = BALI)))
Inv4883 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv4884 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALJ) \/ (~(msg2a(BALK,VALI))))
Inv4885 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALJ) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4887 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv4889 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALK)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv489 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4890 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxBal[ACCI] = BALK)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4891 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4892 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1) \/ (~(msg2b(ACCI,BALK,VALJ))))
Inv4893 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ ((maxBal[ACCI] = BALK))
Inv4894 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ ((maxVBal[ACCI] = BALI))
Inv4895 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ ((msg2b(ACCI,BALK,VALI)))
Inv4896 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4897 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ (~(VALI = None /\ maxBal = maxBal))
Inv4898 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = -1)) \/ (~(msg1a(ACCI,BALK)))
Inv4899 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = BALI) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv4901 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = BALJ) \/ (~(maxVBal[ACCI] > BALJ)))
Inv4902 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] = BALJ) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv4903 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] > BALI) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4904 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] > BALI)) \/ (~(msg1a(ACCI,BALI)))
Inv4905 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] > BALJ) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv4906 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVBal[ACCI] > BALJ) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4910 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVal[ACCI] = VALI) \/ (~(BALI = -1 /\ maxBal = maxBal)))
Inv4912 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVal[ACCI] = VALI) \/ (~(maxVBal[ACCI] > BALI)))
Inv4914 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((maxVal[ACCI] = VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv4919 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1a(ACCI,BALJ))) \/ (~(ChosenAt(BALI, VALI)))
Inv4922 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1a(ACCI,BALK))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4924 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv4925 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALJ)) \/ (~(ChosenAt(BALK, VALI))))
Inv4929 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4933 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg1b(ACCI,BALJ,BALK,VALJ))) \/ (~(maxVBal[ACCI] > BALJ))
Inv4935 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALI,VALI)) \/ (~(ChosenAt(BALI, VALJ))))
Inv4937 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALI,VALI))) \/ (~(maxVBal[ACCI] = BALJ))
Inv4939 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALI,VALJ)) \/ (~(maxVBal[ACCI] = BALI)))
Inv4940 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALI,VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv4941 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALJ,VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv4942 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALJ,VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv4943 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALJ,VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4945 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALJ,VALJ))) \/ (~(msg1a(ACCI,BALI)))
Inv4946 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALJ,VALJ))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv4949 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2a(BALK,VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4950 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(SafeAt(BALK, VALJ))))
Inv4951 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(maxVBal[ACCI] > BALJ)))
Inv4955 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2b(ACCI,BALJ,VALI))) \/ (~(maxVBal[ACCI] > BALJ))
Inv4956 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2b(ACCI,BALJ,VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv4957 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ ((msg2b(ACCI,BALK,VALJ))) \/ (~(SafeAt(BALK, VALJ)))
Inv4958 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv4959 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ ((maxVBal[ACCI] = -1))
Inv4960 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(maxBal[ACCI] < BALI))
Inv4961 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(maxBal[ACCI] < BALK))
Inv4962 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv4963 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv4964 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4965 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < BALK)))
Inv4966 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ ((msg2b(ACCI,BALK,VALI)))
Inv4967 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv4968 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal)) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4969 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALI)))
Inv4970 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((msg1a(ACCI,BALJ)))
Inv4971 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(maxBal[ACCI] < BALK))
Inv4972 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv4973 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(VALI=VALJ /\ maxBal = maxBal))
Inv4974 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)))
Inv4975 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv4976 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALI, VALJ))) \/ ((VALJ = None /\ maxBal = maxBal))
Inv4977 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALJ, VALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv4978 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv4979 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv4980 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((msg1a(ACCI,BALK)))
Inv4981 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALK, VALI))) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv4982 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv4983 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALK, VALJ))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv4984 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALK, VALJ))) \/ (~(msg1a(ACCI,BALI)))
Inv4985 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(BALK, VALJ))) \/ (~(msg2a(BALJ,VALI)))
Inv4986 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(maxBal[ACCI] < BALJ)))
Inv4987 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(maxBal[ACCI] = BALK)))
Inv4988 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(msg2a(BALI,VALJ))))
Inv4989 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(SafeAt(BALK, VALJ)))
Inv4990 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv4991 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv4992 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv4993 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((msg2b(ACCI,BALI,VALJ)))
Inv4994 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv4995 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALI, VALI)) \/ (~(msg2a(BALK,VALJ))))
Inv4998 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALI, VALI))) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv4999 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALI, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)))
Inv5 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALI = -1 /\ maxBal = maxBal) \/ ((BALK = -1 /\ maxBal = maxBal) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv500 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALI) \/ (~(maxVal[ACCI] = VALI)))
Inv5001 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALJ, VALI)) \/ (~(msg2a(BALK,VALI))))
Inv5002 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALJ, VALI)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5003 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALJ, VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5007 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALJ, VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5008 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALJ, VALJ))) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv5009 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(SafeAt(BALK, VALJ))) \/ (~(msg1a(ACCI,BALJ)))
Inv5010 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv5011 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv5014 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = -1)))
Inv5015 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ ((maxVBal[ACCI] = BALJ))
Inv5016 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5017 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALI,VALI)) \/ (~(maxBal[ACCI] < BALK)))
Inv5018 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv5019 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg2a(BALI,VALI))))
Inv5020 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALI,VALJ))) \/ (~(maxBal[ACCI] = -1))
Inv5021 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv5022 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv5023 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(maxBal[ACCI] < BALI))
Inv5024 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(maxBal[ACCI] < BALI)))
Inv5025 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(msg2a(BALK,VALJ))))
Inv5026 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((VALI = None /\ maxBal = maxBal))
Inv5027 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv5028 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((msg1b(ACCI,BALI,BALJ,VALI)))
Inv5029 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5030 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((msg2a(BALI,VALJ)))
Inv5031 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ (~(VALI=VALJ /\ maxBal = maxBal))
Inv5034 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5035 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < BALI) \/ (~(maxBal[ACCI] = BALI)))
Inv5036 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < BALI)) \/ (~(SafeAt(BALK, VALJ)))
Inv5037 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < BALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5040 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < BALK)) \/ (~(msg1a(ACCI,BALJ)))
Inv5041 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI]) \/ (~(msg2a(BALJ,VALJ))))
Inv5042 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ ((msg2a(BALK,VALJ)))
Inv5043 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(SafeAt(BALJ, VALJ)))
Inv5049 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALJ) \/ (~(maxVBal[ACCI] > BALJ)))
Inv505 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALJ) \/ (~(maxVBal[ACCI] > BALI)))
Inv5050 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5051 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALK) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv5052 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALK)) \/ ((maxVBal[ACCI] = -1))
Inv5054 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALK)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5055 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALK)) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv5056 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxBal[ACCI] = BALK)) \/ (~(maxVBal[ACCI] = BALI))
Inv5058 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALI) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5059 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALI)) \/ ((msg2a(BALK,VALJ)))
Inv506 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = -1)) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv5060 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5061 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv5062 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALJ) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5063 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALJ) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv5064 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALJ)) \/ ((msg2b(ACCI,BALK,VALI)))
Inv5065 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5066 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALI)) \/ ((msg1b(ACCI,BALJ,BALK,VALI)))
Inv5067 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(SafeAt(BALI, VALI)))
Inv5068 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(maxBal[ACCI] < BALK))
Inv5069 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(SafeAt(BALI, VALI)))
Inv5070 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(SafeAt(BALJ, VALJ)))
Inv5071 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(msg2a(BALK,VALI)))
Inv5072 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVal[ACCI] = VALI) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5073 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(maxVal[ACCI] = VALI)) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv5074 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ ((maxVBal[ACCI] > BALJ))
Inv5075 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv5076 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv5077 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALI))) \/ (~(msg2a(BALK,VALJ)))
Inv5078 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5079 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1a(ACCI,BALK))) \/ (~(maxBal[ACCI] < BALJ))
Inv5080 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv5081 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((maxBal[ACCI] < maxVBal[ACCI]))
Inv5082 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((maxVBal[ACCI] = -1))
Inv5083 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((msg2a(BALJ,VALJ)))
Inv5084 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv5085 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(ChosenAt(BALK, VALI)))
Inv5086 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv5087 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5088 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv5089 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2a(BALK,VALJ)))
Inv5090 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5091 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((msg2a(BALK,VALJ)))
Inv5092 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ ((VALI = None /\ maxBal = maxBal))
Inv5093 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ ((maxBal[ACCI] = -1))
Inv5094 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5095 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv5099 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALJ,VALI)) \/ (~(msg2a(BALK,VALJ))))
Inv5101 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(VALI=VALJ /\ maxBal = maxBal))
Inv5102 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5103 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALK,VALI))) \/ (~(msg2a(BALJ,VALI)))
Inv5104 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALK,VALJ))) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv5105 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2a(BALK,VALJ))) \/ (~(msg1a(ACCI,BALJ)))
Inv5106 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((maxBal[ACCI] = -1))
Inv5107 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ (~(SafeAt(BALJ, VALI)))
Inv5108 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ (~(ChosenAt(BALJ, VALI)))
Inv5109 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ (~(msg2a(BALI,VALJ)))
Inv511 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = BALJ) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv5110 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ (~(VALI=VALJ /\ maxBal = maxBal))
Inv5111 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ (~(maxBal[ACCI] < BALK))
Inv5112 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((msg1a(ACCI,BALI)))
Inv5113 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ (~(SafeAt(BALI, VALI)))
Inv5114 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv5115 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALI)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ (~(msg1a(ACCI,BALI)))
Inv512 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVBal[ACCI] > BALI) \/ (~(ChosenAt(maxBal[ACCI], VALI))))
Inv5122 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VALI=VALJ /\ maxBal = maxBal)) \/ (~(msg2b(ACCI,BALK,VALI)))
Inv5123 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] > BALJ)))
Inv5124 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv5127 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VALJ = None /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5128 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALI,VALI)) \/ (~(maxVBal[ACCI] > BALJ)))
Inv5130 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALI,VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))))
Inv5135 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALI)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv5138 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(msg1a(ACCI,BALJ)))
Inv5139 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALJ)) \/ (~(maxVBal[ACCI] > BALJ)))
Inv514 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVBal[ACCI] > BALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5141 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALJ))) \/ (~(ChosenAt(BALK, VALJ)))
Inv5142 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALJ,VALJ))) \/ (~(msg1a(ACCI,BALK)))
Inv5146 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((VotedFor(ACCI,BALK,VALJ))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv515 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVBal[ACCI] > BALI)) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv5158 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALJ) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv5159 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALJ) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5162 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK) \/ (~(BALI = -1 /\ maxBal = maxBal)))
Inv5163 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK) \/ (~(ChosenAt(BALI, VALJ))))
Inv5164 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK) \/ (~(ChosenAt(maxVBal[ACCI], VALI))))
Inv5165 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK) \/ (~(msg1a(ACCI,BALI))))
Inv5166 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv5167 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5168 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] < BALK)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5173 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = -1) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv5175 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALI) \/ (~(VotedFor(ACCI,BALJ,VALJ))))
Inv5176 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALI) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv5178 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5180 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALI)) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv5184 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALJ)) \/ (~(ChosenAt(BALJ, VALI)))
Inv5188 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxBal[ACCI] = BALK)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5190 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = -1) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5191 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = -1) \/ (~(msg2a(BALI,VALI))))
Inv5192 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = -1)) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv5193 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = -1)) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv5196 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = BALI)) \/ (~(ChosenAt(BALK, VALJ)))
Inv5197 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] = BALI)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv52 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALI = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALI)) \/ (~(ChosenAt(BALJ, VALJ))))
Inv5200 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVBal[ACCI] > BALI) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv5202 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVal[ACCI] = VALI) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv5203 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((maxVal[ACCI] = VALI)) \/ (~(maxBal[ACCI] < maxVBal[ACCI]))
Inv5204 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1a(ACCI,BALI))) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5205 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1a(ACCI,BALI))) \/ (~(msg2a(BALK,VALI)))
Inv5207 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1a(ACCI,BALJ))) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5209 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1a(ACCI,BALK))) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5210 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5212 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(BALK = -1 /\ maxBal = maxBal))
Inv5213 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg1a(ACCI,BALJ)))
Inv5215 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALI,BALJ,VALJ))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv5217 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALJ,BALK,VALI)) \/ (~(ChosenAt(BALK, VALJ))))
Inv5219 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)) \/ (~(maxVBal[ACCI] = BALJ)))
Inv522 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVal[ACCI] = VALI) \/ (~(VotedFor(ACCI,BALK,VALJ))))
Inv5222 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALI,VALI)) \/ (~(msg1a(ACCI,BALK))))
Inv5225 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALI,VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5228 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALJ,VALI)) \/ (~(ChosenAt(BALI, VALI))))
Inv5229 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALJ,VALI)) \/ (~(ChosenAt(BALK, VALJ))))
Inv523 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVal[ACCI] = VALI) \/ (~(msg1a(ACCI,BALK))))
Inv5230 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALJ,VALI))) \/ (~(maxVBal[ACCI] > BALJ))
Inv5231 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALJ,VALI))) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv5236 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALK,VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5237 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2a(BALK,VALJ)) \/ (~(msg2a(BALK,VALI))))
Inv5238 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALI,VALI)) \/ (~(ChosenAt(BALK, VALI))))
Inv5239 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALI,VALI)) \/ (~(maxVBal[ACCI] > BALI)))
Inv524 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((maxVal[ACCI] = VALI) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5241 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALI,VALI))) \/ (~(maxVBal[ACCI] > BALJ))
Inv5242 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(msg2a(BALK,VALJ))))
Inv5243 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI)) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv5244 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI))) \/ (~(ChosenAt(BALK, VALI)))
Inv5245 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALJ,VALI))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv5248 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALJ,VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5249 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALK,VALI)) \/ (~(maxVal[ACCI] = VALI)))
Inv5251 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALK,VALI))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5254 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ ((msg2b(ACCI,BALK,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5256 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < maxVBal[ACCI])))
Inv5257 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] > BALI)))
Inv5258 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(ChosenAt(BALK, VALJ)))
Inv5259 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5260 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(msg1a(ACCI,BALI)))
Inv5261 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(msg2a(BALJ,VALI)))
Inv5262 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALJ)))
Inv5263 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALI,VALI))))
Inv5264 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5265 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(maxBal[ACCI] = BALK)))
Inv5266 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALK))))
Inv5267 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((maxBal[ACCI] < BALK))
Inv5268 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((msg2a(BALJ,VALI)))
Inv5269 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((msg2a(BALJ,VALJ)))
Inv5270 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = BALI))
Inv5271 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(msg1a(ACCI,BALJ)))
Inv5272 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(maxBal[ACCI] < BALK))
Inv5273 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5274 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(ChosenAt(BALK, VALJ))))
Inv5275 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5276 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALJ)) \/ (~(maxBal[ACCI] = BALI)))
Inv5277 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALJ))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5278 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALI, VALJ))) \/ (~(msg2a(BALI,VALI)))
Inv5279 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALI)) \/ (~(maxBal[ACCI] = BALK)))
Inv5280 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALI)) \/ (~(msg1a(ACCI,BALI))))
Inv5281 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALI))) \/ ((VALI = None /\ maxBal = maxBal))
Inv5282 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(ChosenAt(BALK, VALJ))))
Inv5283 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv5284 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((msg2a(BALI,VALI)))
Inv5285 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((msg2a(BALJ,VALJ)))
Inv5286 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv5287 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALK, VALI))) \/ ((msg2a(BALJ,VALJ)))
Inv5288 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALK, VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv5289 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(maxBal[ACCI] = -1)))
Inv5290 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)))
Inv5291 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(BALK, VALJ))) \/ ((VALI = None /\ maxBal = maxBal))
Inv5292 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ ((VALI = None /\ maxBal = maxBal))
Inv5293 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ ((msg2b(ACCI,BALJ,VALJ)))
Inv5294 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5295 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5296 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv5297 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(SafeAt(BALJ, VALJ))))
Inv5298 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5299 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((VALI=VALJ /\ maxBal = maxBal))
Inv530 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1a(ACCI,BALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv5300 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((VALJ = None /\ maxBal = maxBal))
Inv5304 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(SafeAt(BALI, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5305 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(SafeAt(BALJ, VALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5306 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(SafeAt(BALJ, VALI))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5308 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(SafeAt(BALJ, VALI))) \/ (~(msg2a(BALK,VALJ)))
Inv5312 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(SafeAt(BALJ, VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5313 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = -1))
Inv5314 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALI = None /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5315 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALI=VALJ /\ maxBal = maxBal)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5316 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5317 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ (~(SafeAt(BALK, VALI)))
Inv5318 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ (~(maxVBal[ACCI] = BALI))
Inv5319 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5320 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALI,VALJ))) \/ (~(msg2b(ACCI,BALJ,VALI)))
Inv5321 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv5322 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((maxBal[ACCI] < BALK))
Inv5323 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ (~(maxVBal[ACCI] = -1))
Inv5324 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5325 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv5326 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5327 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((maxVBal[ACCI] > BALI))
Inv5328 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((msg2a(BALI,VALJ)))
Inv5329 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ (~(SafeAt(BALI, VALJ)))
Inv5330 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ (~(msg2b(ACCI,BALJ,VALJ)))
Inv5331 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((VALI=VALJ /\ maxBal = maxBal))
Inv5332 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv5333 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ ((msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5334 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5336 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5338 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(maxVBal[ACCI] = BALJ))
Inv5339 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] < BALI)) \/ (~(maxVBal[ACCI] > BALJ))
Inv5341 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ ((VALJ = None /\ maxBal = maxBal))
Inv5343 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] = -1)) \/ (~(msg1a(ACCI,BALK)))
Inv5344 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] = BALI)) \/ (~(ChosenAt(BALI, VALI)))
Inv5346 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] = BALJ)) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv5347 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxBal[ACCI] = BALJ)) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv5349 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = -1)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5350 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5351 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(maxVal[ACCI] = VALI))
Inv5352 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(msg2a(BALK,VALI)))
Inv5353 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] > BALI)) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)))
Inv5354 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] > BALJ) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5355 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] > BALJ)) \/ (~(ChosenAt(BALK, VALI)))
Inv5356 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ ((msg2a(BALJ,VALI)))
Inv5357 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(maxVal[ACCI] = VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5358 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALI)) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv5359 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ ((msg2b(ACCI,BALK,VALJ)))
Inv536 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv5360 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5361 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ ((msg2b(ACCI,BALJ,VALJ)))
Inv5362 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv5363 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(msg1a(ACCI,BALI)))
Inv5364 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALJ))) \/ (~(msg2a(BALK,VALJ)))
Inv5365 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ ((maxVBal[ACCI] = -1))
Inv5366 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5367 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv5368 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(maxVBal[ACCI] = -1))
Inv5369 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1a(ACCI,BALK))) \/ (~(msg2a(BALK,VALJ)))
Inv537 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALI,BALJ,VALI)) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv5370 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv5371 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(maxVBal[ACCI] = BALI))
Inv5372 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg2a(BALJ,VALJ)))
Inv5373 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv5374 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((VotedFor(ACCI,BALK,VALI)))
Inv5375 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))) \/ ((VotedFor(ACCI,BALK,VALJ)))
Inv5376 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5377 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))) \/ ((maxBal[ACCI] = BALK))
Inv5378 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALI,VALI))) \/ (~(ChosenAt(BALI, VALI)))
Inv5379 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALI,VALI))) \/ (~(ChosenAt(BALJ, VALI)))
Inv5381 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ ((maxBal[ACCI] < BALK))
Inv5383 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALI,VALJ))) \/ (~(SafeAt(BALK, VALI)))
Inv5384 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALJ,VALI))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv5386 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2a(BALK,VALJ))) \/ (~(ChosenAt(BALK, VALI)))
Inv5387 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((VotedFor(ACCI,BALJ,VALI)))
Inv5388 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((maxBal[ACCI] = -1))
Inv5389 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALI,VALI))) \/ ((maxVBal[ACCI] = -1))
Inv5390 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALI,VALJ))) \/ (~(ChosenAt(BALK, VALI)))
Inv5391 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ ((maxBal[ACCI] = BALJ))
Inv5392 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ ((msg2a(BALJ,VALJ)))
Inv5393 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALI))) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5394 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv5395 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALJ,VALJ))) \/ (~(msg2a(BALI,VALI)))
Inv5396 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALK,VALI))) \/ ((maxBal[ACCI] = BALI))
Inv5397 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (SafeAt(BALK, VALJ)) \/ (~(msg2b(ACCI,BALK,VALJ))) \/ ((msg2b(ACCI,BALJ,VALI)))
Inv540 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(maxVBal[ACCI] > BALJ))
Inv5402 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VALJ = None /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5404 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALI,VALI)) \/ (~(ChosenAt(BALK, VALJ))))
Inv5405 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALI,VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv541 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALJ,BALK,VALI)) \/ (~(ChosenAt(BALI, VALI))))
Inv5415 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALJ,VALI)) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5416 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALJ,VALI))) \/ (~(VotedFor(ACCI,BALK,VALI)))
Inv542 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALJ,BALK,VALI)) \/ (~(maxVBal[ACCI] = BALJ)))
Inv5422 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALI))) \/ (~(ChosenAt(BALI, VALJ)))
Inv5423 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((VotedFor(ACCI,BALK,VALI))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5428 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI)) \/ (~(VotedFor(ACCI,BALJ,VALI))))
Inv5433 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(VotedFor(ACCI,BALK,VALJ))))
Inv5434 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(msg2b(ACCI,BALJ,VALJ))))
Inv5435 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv5437 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(maxVBal[ACCI] = BALJ))
Inv5438 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI])) \/ (~(msg2b(ACCI,BALK,VALJ)))
Inv5440 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] < BALI) \/ (~(msg2b(ACCI,BALJ,VALI))))
Inv5442 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] < BALJ)) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv5443 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] < BALK)) \/ (~(msg2b(ACCI,BALI,VALJ)))
Inv5444 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = -1) \/ (~(ChosenAt(maxBal[ACCI], VALI))))
Inv5447 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = -1)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5448 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = -1)) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv5452 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALJ) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5454 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5456 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALK)) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5457 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxBal[ACCI] = BALK)) \/ (~(VotedFor(ACCI,BALJ,VALI)))
Inv5458 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = -1) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv5459 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = -1) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5460 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = -1)) \/ ((maxBal[ACCI] < maxVBal[ACCI]))
Inv5461 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxVBal[ACCI] = -1)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)))
Inv5470 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((maxVal[ACCI] = VALI) \/ (~(BALJ = -1 /\ maxBal = maxBal)))
Inv5475 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1a(ACCI,BALI)) \/ (~(ChosenAt(BALI, VALJ))))
Inv5479 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1a(ACCI,BALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv548 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALI,VALI))) \/ (~(ChosenAt(BALI, VALJ)))
Inv5480 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1a(ACCI,BALJ))) \/ (~(ChosenAt(maxBal[ACCI], VALI)))
Inv5481 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1a(ACCI,BALK))) \/ ((maxVBal[ACCI] = -1))
Inv5482 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALI,BALJ,VALI))) \/ (~(msg1a(ACCI,BALI)))
Inv5483 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALI,BALJ,VALJ)) \/ (~(VotedFor(ACCI,BALK,VALJ))))
Inv5486 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg1b(ACCI,BALJ,BALK,VALJ)) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv549 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALI,VALI))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5494 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2a(BALJ,VALJ)) \/ (~(maxVal[ACCI] = VALI)))
Inv5498 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2a(BALK,VALI)) \/ (~(BALK = -1 /\ maxBal = maxBal)))
Inv5499 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2a(BALK,VALJ)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI))))
Inv550 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALI,VALJ)) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv5501 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALI,VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5504 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALI,VALJ)) \/ (~(maxVBal[ACCI] > BALI)))
Inv5506 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALI,VALJ))) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5507 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALJ,VALI)) \/ (~(ChosenAt(BALK, VALJ))))
Inv5508 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALJ,VALJ)) \/ (~(msg1a(ACCI,BALJ))))
Inv5511 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALJ,VALJ))) \/ (~(ChosenAt(BALJ, VALJ)))
Inv5512 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ ((msg2b(ACCI,BALK,VALI)) \/ (~(VotedFor(ACCI,BALI,VALI))))
Inv5520 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALJ))))
Inv5521 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALI = -1 /\ maxBal = maxBal) \/ (~(msg2a(BALK,VALJ))))
Inv5522 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALI = -1 /\ maxBal = maxBal)) \/ (~(msg2a(BALI,VALI)))
Inv5523 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALJ = -1 /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALJ))))
Inv5524 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(ChosenAt(BALI, VALJ))))
Inv5525 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI))))
Inv5526 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ ((msg2b(ACCI,BALI,VALJ)))
Inv5527 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(BALK = -1 /\ maxBal = maxBal)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI)))
Inv5528 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALI, VALI))) \/ ((maxBal[ACCI] = BALJ))
Inv5529 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALI, VALI))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv5530 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALI, VALI))) \/ (~(msg1a(ACCI,BALI)))
Inv5531 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALJ, VALI))) \/ (~(BALI = -1 /\ maxBal = maxBal))
Inv5532 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALJ, VALJ)) \/ (~(SafeAt(BALI, VALJ))))
Inv5533 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALJ, VALJ))) \/ ((maxBal[ACCI] < BALJ))
Inv5534 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALI)) \/ (~(msg1b(ACCI,BALI,BALJ,VALI))))
Inv5535 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALI)) \/ (~(msg2a(BALK,VALJ))))
Inv5536 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALI))) \/ (~(maxBal[ACCI] = -1))
Inv5537 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv5538 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALJ)) \/ (~(maxVBal[ACCI] = BALI)))
Inv5539 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(BALK, VALJ))) \/ ((msg1a(ACCI,BALI)))
Inv554 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALJ,VALI)) \/ (~(VALI = None /\ maxBal = maxBal)))
Inv5540 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxBal[ACCI], VALI)) \/ (~(maxVBal[ACCI] > BALI)))
Inv5541 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxBal[ACCI], VALI))) \/ ((VotedFor(ACCI,BALI,VALJ)))
Inv5542 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(SafeAt(BALI, VALI))))
Inv5543 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(maxBal[ACCI] = BALI)))
Inv5544 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ))))
Inv5545 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ ((maxVBal[ACCI] = BALI))
Inv5546 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(ChosenAt(maxVBal[ACCI], VALI))) \/ (~(maxBal[ACCI] = -1))
Inv5549 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALI, VALI))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5551 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALI, VALJ))) \/ (~(VotedFor(ACCI,BALJ,VALJ)))
Inv5552 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALI, VALJ))) \/ (~(maxVal[ACCI] = VALI))
Inv5553 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALI, VALJ))) \/ (~(msg1a(ACCI,BALJ)))
Inv5554 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALJ, VALI)) \/ (~(VotedFor(ACCI,BALI,VALI))))
Inv5556 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALK, VALI))) \/ (~(msg2b(ACCI,BALI,VALI)))
Inv5557 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(SafeAt(BALK, VALJ))) \/ (~(VotedFor(ACCI,BALK,VALJ)))
Inv5558 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VALI=VALJ /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv556 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALJ,VALJ)) \/ (~(ChosenAt(BALK, VALI))))
Inv5560 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VALI=VALJ /\ maxBal = maxBal)) \/ (~(ChosenAt(BALI, VALI)))
Inv5562 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal) \/ (~(msg2b(ACCI,BALI,VALJ))))
Inv5563 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv5564 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VALJ = None /\ maxBal = maxBal)) \/ ((msg1b(ACCI,BALI,BALJ,VALI)))
Inv5565 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((VotedFor(ACCI,BALK,VALJ)))
Inv5566 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALI))) \/ ((maxVBal[ACCI] = -1))
Inv5567 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(VotedFor(ACCI,BALK,VALI))))
Inv5568 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALJ)) \/ (~(msg2a(BALJ,VALJ))))
Inv5569 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALI,VALJ))) \/ ((maxVBal[ACCI] > BALJ))
Inv5570 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv5571 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALJ,VALI))) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5572 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALJ,VALJ)) \/ (~(msg2a(BALK,VALI))))
Inv5573 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALJ,VALJ))) \/ ((msg2a(BALJ,VALI)))
Inv5574 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALK,VALI)) \/ (~(msg1a(ACCI,BALJ))))
Inv5575 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(VotedFor(ACCI,BALK,VALI))) \/ ((msg1a(ACCI,BALI)))
Inv5577 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(\E Q \in Quorum : ShowsSafeAt(Q, maxBal[ACCI], VALI))) \/ ((\E m \in msgs : m.bal >= maxBal[ACCI]))
Inv558 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALJ = -1 /\ maxBal = maxBal) \/ ((msg2a(BALJ,VALJ))) \/ (~(VALI = None /\ maxBal = maxBal))
Inv5580 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < BALJ) \/ (~(msg1a(ACCI,BALJ))))
Inv5582 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < BALJ)) \/ (~(msg1a(ACCI,BALI)))
Inv5583 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxBal[ACCI] < maxVBal[ACCI])) \/ (~(maxVBal[ACCI] = -1))
Inv5584 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxBal[ACCI] = -1) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ))))
Inv5591 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = -1)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5592 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = -1)) \/ (~(msg1b(ACCI,BALJ,BALK,VALJ)))
Inv5594 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALI)) \/ ((maxVBal[ACCI] > BALJ))
Inv5595 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALI)) \/ ((msg2a(BALK,VALI)))
Inv5596 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALI)) \/ (~(msg1b(ACCI,BALJ,BALK,VALI)))
Inv5597 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(ChosenAt(maxVBal[ACCI], VALI)))
Inv5598 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] = BALJ)) \/ (~(VALJ = None /\ maxBal = maxBal))
Inv5599 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVBal[ACCI] > BALI)) \/ ((maxBal[ACCI] < BALI))
Inv56 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (BALI = -1 /\ maxBal = maxBal) \/ ((SafeAt(BALJ, VALJ))) \/ (~(msg1b(ACCI,BALI,BALJ,VALJ)))
Inv5600 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI) \/ (~(msg2b(ACCI,BALK,VALI))))
Inv5601 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI)) \/ (~(BALJ = -1 /\ maxBal = maxBal))
Inv5602 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(maxVal[ACCI] = VALI)) \/ (~(VotedFor(ACCI,BALI,VALI)))
Inv5603 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALI)) \/ (~(msg2a(BALJ,VALJ))))
Inv5604 == \A ACCI \in Acceptor : \A VALI \in Value : \A VALJ \in Value : \A BALI \in Ballot : \A BALJ \in Ballot : \A BALK \in Ballot : (VALI = None /\ maxBal = maxBal) \/ (~(msg1a(ACCI,BALI))) \/ ((VotedFor(ACCI,BALI,VALI)))

kCTIs == 
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> 0) /\ msgs = {} /\ maxBal = (a1 :> 1 @@ a2 :> 2 @@ a3 :> 0)
	   /\ ctiId = "-3016737868961240364"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 1],   [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "2234774298909600483"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> 0, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "-4289006909845959962"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "2a", bal |-> 0, val |-> v1],   [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 0)
	   /\ ctiId = "2691189743179799271"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> -1) /\ msgs = { [type |-> "2a", bal |-> 1, val |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 2 @@ a3 :> -1)
	   /\ ctiId = "-7012944299053444373"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "-5278618295724870930"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 0)
	   /\ ctiId = "-2807922675371398417"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> None) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 0, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 0 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "8752601053970201333"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 0 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "-2961980770203168011"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "4393652559586536185"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> None) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 1, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 0, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "-7467569523809182950"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 0)
	   /\ ctiId = "4311456261503908635"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> 0) /\ msgs = { [type |-> "2b", bal |-> 1, acc |-> a2, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 0 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "645129391796964123"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> v1] } /\ maxBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> -1)
	   /\ ctiId = "-8295875583824708828"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> -1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 1, acc |-> a2, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 2 @@ a3 :> 0)
	   /\ ctiId = "5402097052178068262"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "2a", bal |-> 0, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "-2998098956532434135"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0) /\ msgs = {[type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v1]} /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "6747303825994810154"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 1],   [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1],   [type |-> "2b", bal |-> 1, acc |-> a1, val |-> v1] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "8503787813030019885"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0) /\ msgs = {[type |-> "1a", bal |-> 2], [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v1]} /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "-7945858489546542289"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 1],   [type |-> "2a", bal |-> 0, val |-> v1],   [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v2],   [type |-> "2b", bal |-> 0, acc |-> a3, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "-3556304757976407247"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 1, acc |-> a3, val |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "-7663447157224273100"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 2, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "3289436927056108340"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> None) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 0, acc |-> a3, val |-> v2],   [type |-> "2b", bal |-> 1, acc |-> a1, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 0 @@ a2 :> 1 @@ a3 :> 2)
	   /\ ctiId = "-8196095711204568265"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 0 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "5541638841196221240"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 1],   [type |-> "2a", bal |-> 0, val |-> v1],   [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "-2202756647620687043"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> None) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> -1) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "2a", bal |-> 0, val |-> v2],   [type |-> "2b", bal |-> 1, acc |-> a2, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "1833637119962358597"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 0)
	   /\ ctiId = "657050600107391834"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "2a", bal |-> 0, val |-> v2],   [type |-> "2b", bal |-> 2, acc |-> a2, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "-7615537896875766947"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = {} /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "-4254124983768814742"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 1],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "-2743938028360737942"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 1) /\ msgs = {} /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "5248652512024073069"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 2 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v2],   [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 2 @@ a3 :> 0)
	   /\ ctiId = "7149615889898120046"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1) /\ msgs = { [type |-> "2a", bal |-> 1, val |-> v1],   [type |-> "2b", bal |-> 1, acc |-> a2, val |-> v1],   [type |-> "2b", bal |-> 1, acc |-> a2, val |-> v2],   [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> 2, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> 0, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "-1634514221236868241"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> -1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "2b", bal |-> 2, acc |-> a2, val |-> v2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> v1] } /\ maxBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "-5751038754372234382"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "-256918522695308424"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 1 @@ a3 :> 1)
	   /\ ctiId = "9080294704178404223"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "2b", bal |-> 2, acc |-> a1, val |-> v2],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "5537269698023140225"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1a", bal |-> 2],   [type |-> "2b", bal |-> 1, acc |-> a3, val |-> v2] } /\ maxBal = (a1 :> 0 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "-6042397580172029055"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v2],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v1] } /\ maxBal = (a1 :> 1 @@ a2 :> 2 @@ a3 :> 0)
	   /\ ctiId = "2233515795800898438"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 1],   [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 0)
	   /\ ctiId = "-1328619768770303094"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> None) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1) /\ msgs = { [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1],   [type |-> "2b", bal |-> 2, acc |-> a2, val |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a1, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 2, acc |-> a2, mbal |-> -1, mval |-> v2] } /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "3477694263112668051"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "2a", bal |-> 0, val |-> v1],   [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v2],   [type |-> "2b", bal |-> 0, acc |-> a3, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> v1],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> -1, mval |-> None] } /\ maxBal = (a1 :> -1 @@ a2 :> 0 @@ a3 :> 0)
	   /\ ctiId = "-7821618126808689763"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 0],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> -1, mval |-> None],   [type |-> "1b", bal |-> 2, acc |-> a3, mbal |-> 2, mval |-> None] } /\ maxBal = (a1 :> 0 @@ a2 :> 2 @@ a3 :> 1)
	   /\ ctiId = "-558150643846941792"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> -1 @@ a2 :> -1 @@ a3 :> 1) /\ msgs = { [type |-> "1a", bal |-> 2],   [type |-> "1b", bal |-> 1, acc |-> a3, mbal |-> 2, mval |-> None] } /\ maxBal = (a1 :> 2 @@ a2 :> 0 @@ a3 :> 1)
	   /\ ctiId = "4232609552001562618"
	\/ /\ maxVal = (a1 :> None @@ a2 :> None @@ a3 :> v1) /\ maxVBal = (a1 :> 0 @@ a2 :> -1 @@ a3 :> 0) /\ msgs = { [type |-> "1a", bal |-> 1],   [type |-> "2b", bal |-> 0, acc |-> a2, val |-> v1],   [type |-> "1b", bal |-> 0, acc |-> a3, mbal |-> 2, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a1, mbal |-> 1, mval |-> None],   [type |-> "1b", bal |-> 1, acc |-> a2, mbal |-> 2, mval |-> None] } /\ maxBal = (a1 :> 1 @@ a2 :> 1 @@ a3 :> 0)
	   /\ ctiId = "4065659014864982946"


InvVals ==
	    /\ TRUE
	   /\ Inv4149_val = Inv4149
	   /\ Inv415_val = Inv415
	   /\ Inv4150_val = Inv4150
	   /\ Inv4151_val = Inv4151
	   /\ Inv4152_val = Inv4152
	   /\ Inv4153_val = Inv4153
	   /\ Inv4154_val = Inv4154
	   /\ Inv4155_val = Inv4155
	   /\ Inv4156_val = Inv4156
	   /\ Inv416_val = Inv416
	   /\ Inv4160_val = Inv4160
	   /\ Inv4161_val = Inv4161
	   /\ Inv4163_val = Inv4163
	   /\ Inv4164_val = Inv4164
	   /\ Inv4166_val = Inv4166
	   /\ Inv4170_val = Inv4170
	   /\ Inv4171_val = Inv4171
	   /\ Inv4172_val = Inv4172
	   /\ Inv4173_val = Inv4173
	   /\ Inv4174_val = Inv4174
	   /\ Inv4175_val = Inv4175
	   /\ Inv4176_val = Inv4176
	   /\ Inv4177_val = Inv4177
	   /\ Inv4178_val = Inv4178
	   /\ Inv4179_val = Inv4179
	   /\ Inv4180_val = Inv4180
	   /\ Inv4181_val = Inv4181
	   /\ Inv4182_val = Inv4182
	   /\ Inv4183_val = Inv4183
	   /\ Inv4184_val = Inv4184
	   /\ Inv4185_val = Inv4185
	   /\ Inv4186_val = Inv4186
	   /\ Inv4187_val = Inv4187
	   /\ Inv4188_val = Inv4188
	   /\ Inv4189_val = Inv4189
	   /\ Inv4190_val = Inv4190
	   /\ Inv4191_val = Inv4191
	   /\ Inv4192_val = Inv4192
	   /\ Inv4193_val = Inv4193
	   /\ Inv4194_val = Inv4194
	   /\ Inv4195_val = Inv4195
	   /\ Inv4196_val = Inv4196
	   /\ Inv4197_val = Inv4197
	   /\ Inv4198_val = Inv4198
	   /\ Inv4199_val = Inv4199
	   /\ Inv4200_val = Inv4200
	   /\ Inv4201_val = Inv4201
	   /\ Inv4202_val = Inv4202
	   /\ Inv4203_val = Inv4203
	   /\ Inv4204_val = Inv4204
	   /\ Inv4205_val = Inv4205
	   /\ Inv4206_val = Inv4206
	   /\ Inv4207_val = Inv4207
	   /\ Inv4208_val = Inv4208
	   /\ Inv4209_val = Inv4209
	   /\ Inv421_val = Inv421
	   /\ Inv4210_val = Inv4210
	   /\ Inv4211_val = Inv4211
	   /\ Inv4218_val = Inv4218
	   /\ Inv4221_val = Inv4221
	   /\ Inv4222_val = Inv4222
	   /\ Inv4223_val = Inv4223
	   /\ Inv4224_val = Inv4224
	   /\ Inv4225_val = Inv4225
	   /\ Inv4226_val = Inv4226
	   /\ Inv4227_val = Inv4227
	   /\ Inv4228_val = Inv4228
	   /\ Inv4229_val = Inv4229
	   /\ Inv4230_val = Inv4230
	   /\ Inv4231_val = Inv4231
	   /\ Inv4232_val = Inv4232
	   /\ Inv4233_val = Inv4233
	   /\ Inv4234_val = Inv4234
	   /\ Inv4237_val = Inv4237
	   /\ Inv4238_val = Inv4238
	   /\ Inv4239_val = Inv4239
	   /\ Inv424_val = Inv424
	   /\ Inv4240_val = Inv4240
	   /\ Inv4241_val = Inv4241
	   /\ Inv4244_val = Inv4244
	   /\ Inv4247_val = Inv4247
	   /\ Inv4249_val = Inv4249
	   /\ Inv4250_val = Inv4250
	   /\ Inv4251_val = Inv4251
	   /\ Inv4255_val = Inv4255
	   /\ Inv4270_val = Inv4270
	   /\ Inv4273_val = Inv4273
	   /\ Inv4275_val = Inv4275
	   /\ Inv4277_val = Inv4277
	   /\ Inv4278_val = Inv4278
	   /\ Inv428_val = Inv428
	   /\ Inv4280_val = Inv4280
	   /\ Inv4281_val = Inv4281
	   /\ Inv4288_val = Inv4288
	   /\ Inv4290_val = Inv4290
	   /\ Inv4291_val = Inv4291
	   /\ Inv4292_val = Inv4292
	   /\ Inv4302_val = Inv4302
	   /\ Inv4303_val = Inv4303
	   /\ Inv4308_val = Inv4308
	   /\ Inv4311_val = Inv4311
	   /\ Inv4312_val = Inv4312
	   /\ Inv4314_val = Inv4314
	   /\ Inv4318_val = Inv4318
	   /\ Inv4319_val = Inv4319
	   /\ Inv432_val = Inv432
	   /\ Inv4321_val = Inv4321
	   /\ Inv4323_val = Inv4323
	   /\ Inv4324_val = Inv4324
	   /\ Inv4329_val = Inv4329
	   /\ Inv433_val = Inv433
	   /\ Inv4330_val = Inv4330
	   /\ Inv4331_val = Inv4331
	   /\ Inv4332_val = Inv4332
	   /\ Inv4333_val = Inv4333
	   /\ Inv434_val = Inv434
	   /\ Inv4340_val = Inv4340
	   /\ Inv4343_val = Inv4343
	   /\ Inv4345_val = Inv4345
	   /\ Inv4346_val = Inv4346
	   /\ Inv4347_val = Inv4347
	   /\ Inv4348_val = Inv4348
	   /\ Inv4352_val = Inv4352
	   /\ Inv4353_val = Inv4353
	   /\ Inv4354_val = Inv4354
	   /\ Inv4357_val = Inv4357
	   /\ Inv4358_val = Inv4358
	   /\ Inv4359_val = Inv4359
	   /\ Inv4360_val = Inv4360
	   /\ Inv4361_val = Inv4361
	   /\ Inv4364_val = Inv4364
	   /\ Inv4366_val = Inv4366
	   /\ Inv437_val = Inv437
	   /\ Inv4370_val = Inv4370
	   /\ Inv4371_val = Inv4371
	   /\ Inv4372_val = Inv4372
	   /\ Inv4373_val = Inv4373
	   /\ Inv4375_val = Inv4375
	   /\ Inv4376_val = Inv4376
	   /\ Inv4378_val = Inv4378
	   /\ Inv4379_val = Inv4379
	   /\ Inv438_val = Inv438
	   /\ Inv4380_val = Inv4380
	   /\ Inv4381_val = Inv4381
	   /\ Inv4382_val = Inv4382
	   /\ Inv4383_val = Inv4383
	   /\ Inv4384_val = Inv4384
	   /\ Inv4385_val = Inv4385
	   /\ Inv4386_val = Inv4386
	   /\ Inv4387_val = Inv4387
	   /\ Inv4388_val = Inv4388
	   /\ Inv4389_val = Inv4389
	   /\ Inv4390_val = Inv4390
	   /\ Inv4391_val = Inv4391
	   /\ Inv4392_val = Inv4392
	   /\ Inv4393_val = Inv4393
	   /\ Inv4394_val = Inv4394
	   /\ Inv4395_val = Inv4395
	   /\ Inv4396_val = Inv4396
	   /\ Inv4397_val = Inv4397
	   /\ Inv4398_val = Inv4398
	   /\ Inv4399_val = Inv4399
	   /\ Inv440_val = Inv440
	   /\ Inv4400_val = Inv4400
	   /\ Inv4401_val = Inv4401
	   /\ Inv4402_val = Inv4402
	   /\ Inv4403_val = Inv4403
	   /\ Inv4404_val = Inv4404
	   /\ Inv4405_val = Inv4405
	   /\ Inv4406_val = Inv4406
	   /\ Inv4407_val = Inv4407
	   /\ Inv4408_val = Inv4408
	   /\ Inv4409_val = Inv4409
	   /\ Inv4410_val = Inv4410
	   /\ Inv4411_val = Inv4411
	   /\ Inv4412_val = Inv4412
	   /\ Inv4414_val = Inv4414
	   /\ Inv4415_val = Inv4415
	   /\ Inv4416_val = Inv4416
	   /\ Inv4417_val = Inv4417
	   /\ Inv4418_val = Inv4418
	   /\ Inv4420_val = Inv4420
	   /\ Inv4421_val = Inv4421
	   /\ Inv4424_val = Inv4424
	   /\ Inv4425_val = Inv4425
	   /\ Inv4426_val = Inv4426
	   /\ Inv4427_val = Inv4427
	   /\ Inv4428_val = Inv4428
	   /\ Inv4429_val = Inv4429
	   /\ Inv4430_val = Inv4430
	   /\ Inv4431_val = Inv4431
	   /\ Inv4432_val = Inv4432
	   /\ Inv4433_val = Inv4433
	   /\ Inv4434_val = Inv4434
	   /\ Inv4435_val = Inv4435
	   /\ Inv4436_val = Inv4436
	   /\ Inv4437_val = Inv4437
	   /\ Inv4438_val = Inv4438
	   /\ Inv4440_val = Inv4440
	   /\ Inv4442_val = Inv4442
	   /\ Inv4444_val = Inv4444
	   /\ Inv4445_val = Inv4445
	   /\ Inv4446_val = Inv4446
	   /\ Inv4448_val = Inv4448
	   /\ Inv4449_val = Inv4449
	   /\ Inv445_val = Inv445
	   /\ Inv4450_val = Inv4450
	   /\ Inv4451_val = Inv4451
	   /\ Inv4452_val = Inv4452
	   /\ Inv4453_val = Inv4453
	   /\ Inv4455_val = Inv4455
	   /\ Inv4456_val = Inv4456
	   /\ Inv4458_val = Inv4458
	   /\ Inv4463_val = Inv4463
	   /\ Inv4464_val = Inv4464
	   /\ Inv4465_val = Inv4465
	   /\ Inv4466_val = Inv4466
	   /\ Inv4467_val = Inv4467
	   /\ Inv4468_val = Inv4468
	   /\ Inv4469_val = Inv4469
	   /\ Inv4470_val = Inv4470
	   /\ Inv4471_val = Inv4471
	   /\ Inv4472_val = Inv4472
	   /\ Inv4473_val = Inv4473
	   /\ Inv4474_val = Inv4474
	   /\ Inv4475_val = Inv4475
	   /\ Inv4476_val = Inv4476
	   /\ Inv4477_val = Inv4477
	   /\ Inv4478_val = Inv4478
	   /\ Inv4479_val = Inv4479
	   /\ Inv448_val = Inv448
	   /\ Inv4480_val = Inv4480
	   /\ Inv4481_val = Inv4481
	   /\ Inv4482_val = Inv4482
	   /\ Inv4483_val = Inv4483
	   /\ Inv4484_val = Inv4484
	   /\ Inv4485_val = Inv4485
	   /\ Inv4488_val = Inv4488
	   /\ Inv4489_val = Inv4489
	   /\ Inv4490_val = Inv4490
	   /\ Inv4491_val = Inv4491
	   /\ Inv4492_val = Inv4492
	   /\ Inv4493_val = Inv4493
	   /\ Inv4494_val = Inv4494
	   /\ Inv4495_val = Inv4495
	   /\ Inv4496_val = Inv4496
	   /\ Inv4497_val = Inv4497
	   /\ Inv4498_val = Inv4498
	   /\ Inv4499_val = Inv4499
	   /\ Inv4501_val = Inv4501
	   /\ Inv4502_val = Inv4502
	   /\ Inv4503_val = Inv4503
	   /\ Inv4504_val = Inv4504
	   /\ Inv4505_val = Inv4505
	   /\ Inv4506_val = Inv4506
	   /\ Inv4507_val = Inv4507
	   /\ Inv4508_val = Inv4508
	   /\ Inv4509_val = Inv4509
	   /\ Inv4513_val = Inv4513
	   /\ Inv4516_val = Inv4516
	   /\ Inv4518_val = Inv4518
	   /\ Inv4519_val = Inv4519
	   /\ Inv4520_val = Inv4520
	   /\ Inv4521_val = Inv4521
	   /\ Inv4522_val = Inv4522
	   /\ Inv4525_val = Inv4525
	   /\ Inv4527_val = Inv4527
	   /\ Inv4535_val = Inv4535
	   /\ Inv4537_val = Inv4537
	   /\ Inv4538_val = Inv4538
	   /\ Inv4544_val = Inv4544
	   /\ Inv4547_val = Inv4547
	   /\ Inv4548_val = Inv4548
	   /\ Inv455_val = Inv455
	   /\ Inv4551_val = Inv4551
	   /\ Inv4553_val = Inv4553
	   /\ Inv4559_val = Inv4559
	   /\ Inv4560_val = Inv4560
	   /\ Inv4561_val = Inv4561
	   /\ Inv4562_val = Inv4562
	   /\ Inv4567_val = Inv4567
	   /\ Inv4571_val = Inv4571
	   /\ Inv4572_val = Inv4572
	   /\ Inv4577_val = Inv4577
	   /\ Inv4579_val = Inv4579
	   /\ Inv458_val = Inv458
	   /\ Inv4581_val = Inv4581
	   /\ Inv4583_val = Inv4583
	   /\ Inv4586_val = Inv4586
	   /\ Inv4587_val = Inv4587
	   /\ Inv4590_val = Inv4590
	   /\ Inv4592_val = Inv4592
	   /\ Inv4593_val = Inv4593
	   /\ Inv4594_val = Inv4594
	   /\ Inv4596_val = Inv4596
	   /\ Inv4597_val = Inv4597
	   /\ Inv4598_val = Inv4598
	   /\ Inv46_val = Inv46
	   /\ Inv4602_val = Inv4602
	   /\ Inv4604_val = Inv4604
	   /\ Inv4609_val = Inv4609
	   /\ Inv4610_val = Inv4610
	   /\ Inv4611_val = Inv4611
	   /\ Inv4619_val = Inv4619
	   /\ Inv4620_val = Inv4620
	   /\ Inv4625_val = Inv4625
	   /\ Inv4626_val = Inv4626
	   /\ Inv4627_val = Inv4627
	   /\ Inv4629_val = Inv4629
	   /\ Inv4631_val = Inv4631
	   /\ Inv4633_val = Inv4633
	   /\ Inv4634_val = Inv4634
	   /\ Inv4636_val = Inv4636
	   /\ Inv4638_val = Inv4638
	   /\ Inv4639_val = Inv4639
	   /\ Inv4641_val = Inv4641
	   /\ Inv4644_val = Inv4644
	   /\ Inv4645_val = Inv4645
	   /\ Inv4647_val = Inv4647
	   /\ Inv4648_val = Inv4648
	   /\ Inv4651_val = Inv4651
	   /\ Inv4652_val = Inv4652
	   /\ Inv4653_val = Inv4653
	   /\ Inv4655_val = Inv4655
	   /\ Inv4656_val = Inv4656
	   /\ Inv4657_val = Inv4657
	   /\ Inv4658_val = Inv4658
	   /\ Inv4659_val = Inv4659
	   /\ Inv4660_val = Inv4660
	   /\ Inv4661_val = Inv4661
	   /\ Inv4662_val = Inv4662
	   /\ Inv4663_val = Inv4663
	   /\ Inv4664_val = Inv4664
	   /\ Inv4665_val = Inv4665
	   /\ Inv4666_val = Inv4666
	   /\ Inv4667_val = Inv4667
	   /\ Inv4668_val = Inv4668
	   /\ Inv4669_val = Inv4669
	   /\ Inv4670_val = Inv4670
	   /\ Inv4671_val = Inv4671
	   /\ Inv4672_val = Inv4672
	   /\ Inv4673_val = Inv4673
	   /\ Inv4674_val = Inv4674
	   /\ Inv4675_val = Inv4675
	   /\ Inv4676_val = Inv4676
	   /\ Inv4677_val = Inv4677
	   /\ Inv4678_val = Inv4678
	   /\ Inv4679_val = Inv4679
	   /\ Inv468_val = Inv468
	   /\ Inv4680_val = Inv4680
	   /\ Inv4681_val = Inv4681
	   /\ Inv4683_val = Inv4683
	   /\ Inv4686_val = Inv4686
	   /\ Inv4687_val = Inv4687
	   /\ Inv4688_val = Inv4688
	   /\ Inv4689_val = Inv4689
	   /\ Inv4692_val = Inv4692
	   /\ Inv4693_val = Inv4693
	   /\ Inv4695_val = Inv4695
	   /\ Inv4696_val = Inv4696
	   /\ Inv4697_val = Inv4697
	   /\ Inv4698_val = Inv4698
	   /\ Inv4699_val = Inv4699
	   /\ Inv47_val = Inv47
	   /\ Inv4702_val = Inv4702
	   /\ Inv4704_val = Inv4704
	   /\ Inv4705_val = Inv4705
	   /\ Inv4706_val = Inv4706
	   /\ Inv4707_val = Inv4707
	   /\ Inv4708_val = Inv4708
	   /\ Inv4709_val = Inv4709
	   /\ Inv4710_val = Inv4710
	   /\ Inv4711_val = Inv4711
	   /\ Inv4712_val = Inv4712
	   /\ Inv4713_val = Inv4713
	   /\ Inv4714_val = Inv4714
	   /\ Inv4715_val = Inv4715
	   /\ Inv4716_val = Inv4716
	   /\ Inv4717_val = Inv4717
	   /\ Inv4718_val = Inv4718
	   /\ Inv4719_val = Inv4719
	   /\ Inv4720_val = Inv4720
	   /\ Inv4721_val = Inv4721
	   /\ Inv4722_val = Inv4722
	   /\ Inv4723_val = Inv4723
	   /\ Inv4724_val = Inv4724
	   /\ Inv4725_val = Inv4725
	   /\ Inv4726_val = Inv4726
	   /\ Inv4728_val = Inv4728
	   /\ Inv4729_val = Inv4729
	   /\ Inv473_val = Inv473
	   /\ Inv4733_val = Inv4733
	   /\ Inv4735_val = Inv4735
	   /\ Inv4736_val = Inv4736
	   /\ Inv4738_val = Inv4738
	   /\ Inv4739_val = Inv4739
	   /\ Inv4740_val = Inv4740
	   /\ Inv4741_val = Inv4741
	   /\ Inv4742_val = Inv4742
	   /\ Inv4743_val = Inv4743
	   /\ Inv4744_val = Inv4744
	   /\ Inv4745_val = Inv4745
	   /\ Inv4748_val = Inv4748
	   /\ Inv4749_val = Inv4749
	   /\ Inv475_val = Inv475
	   /\ Inv4751_val = Inv4751
	   /\ Inv4758_val = Inv4758
	   /\ Inv4759_val = Inv4759
	   /\ Inv476_val = Inv476
	   /\ Inv4760_val = Inv4760
	   /\ Inv4761_val = Inv4761
	   /\ Inv4762_val = Inv4762
	   /\ Inv4763_val = Inv4763
	   /\ Inv4764_val = Inv4764
	   /\ Inv4765_val = Inv4765
	   /\ Inv4766_val = Inv4766
	   /\ Inv4767_val = Inv4767
	   /\ Inv4768_val = Inv4768
	   /\ Inv4769_val = Inv4769
	   /\ Inv4770_val = Inv4770
	   /\ Inv4771_val = Inv4771
	   /\ Inv4772_val = Inv4772
	   /\ Inv4773_val = Inv4773
	   /\ Inv4774_val = Inv4774
	   /\ Inv4775_val = Inv4775
	   /\ Inv4776_val = Inv4776
	   /\ Inv4777_val = Inv4777
	   /\ Inv4778_val = Inv4778
	   /\ Inv4779_val = Inv4779
	   /\ Inv4780_val = Inv4780
	   /\ Inv4781_val = Inv4781
	   /\ Inv4782_val = Inv4782
	   /\ Inv4783_val = Inv4783
	   /\ Inv4784_val = Inv4784
	   /\ Inv4785_val = Inv4785
	   /\ Inv4786_val = Inv4786
	   /\ Inv4789_val = Inv4789
	   /\ Inv479_val = Inv479
	   /\ Inv4790_val = Inv4790
	   /\ Inv4791_val = Inv4791
	   /\ Inv4792_val = Inv4792
	   /\ Inv4794_val = Inv4794
	   /\ Inv4796_val = Inv4796
	   /\ Inv4797_val = Inv4797
	   /\ Inv4798_val = Inv4798
	   /\ Inv4799_val = Inv4799
	   /\ Inv480_val = Inv480
	   /\ Inv4800_val = Inv4800
	   /\ Inv4801_val = Inv4801
	   /\ Inv4802_val = Inv4802
	   /\ Inv4803_val = Inv4803
	   /\ Inv4804_val = Inv4804
	   /\ Inv4805_val = Inv4805
	   /\ Inv4806_val = Inv4806
	   /\ Inv4807_val = Inv4807
	   /\ Inv4809_val = Inv4809
	   /\ Inv4819_val = Inv4819
	   /\ Inv482_val = Inv482
	   /\ Inv4820_val = Inv4820
	   /\ Inv4821_val = Inv4821
	   /\ Inv4823_val = Inv4823
	   /\ Inv4827_val = Inv4827
	   /\ Inv4828_val = Inv4828
	   /\ Inv4831_val = Inv4831
	   /\ Inv4833_val = Inv4833
	   /\ Inv4837_val = Inv4837
	   /\ Inv4839_val = Inv4839
	   /\ Inv4840_val = Inv4840
	   /\ Inv4841_val = Inv4841
	   /\ Inv4842_val = Inv4842
	   /\ Inv4844_val = Inv4844
	   /\ Inv4847_val = Inv4847
	   /\ Inv485_val = Inv485
	   /\ Inv4850_val = Inv4850
	   /\ Inv4854_val = Inv4854
	   /\ Inv4858_val = Inv4858
	   /\ Inv4859_val = Inv4859
	   /\ Inv4861_val = Inv4861
	   /\ Inv4865_val = Inv4865
	   /\ Inv4868_val = Inv4868
	   /\ Inv4869_val = Inv4869
	   /\ Inv487_val = Inv487
	   /\ Inv4872_val = Inv4872
	   /\ Inv4874_val = Inv4874
	   /\ Inv4875_val = Inv4875
	   /\ Inv4877_val = Inv4877
	   /\ Inv4879_val = Inv4879
	   /\ Inv488_val = Inv488
	   /\ Inv4881_val = Inv4881
	   /\ Inv4883_val = Inv4883
	   /\ Inv4884_val = Inv4884
	   /\ Inv4885_val = Inv4885
	   /\ Inv4887_val = Inv4887
	   /\ Inv4889_val = Inv4889
	   /\ Inv489_val = Inv489
	   /\ Inv4890_val = Inv4890
	   /\ Inv4891_val = Inv4891
	   /\ Inv4892_val = Inv4892
	   /\ Inv4893_val = Inv4893
	   /\ Inv4894_val = Inv4894
	   /\ Inv4895_val = Inv4895
	   /\ Inv4896_val = Inv4896
	   /\ Inv4897_val = Inv4897
	   /\ Inv4898_val = Inv4898
	   /\ Inv4899_val = Inv4899
	   /\ Inv4901_val = Inv4901
	   /\ Inv4902_val = Inv4902
	   /\ Inv4903_val = Inv4903
	   /\ Inv4904_val = Inv4904
	   /\ Inv4905_val = Inv4905
	   /\ Inv4906_val = Inv4906
	   /\ Inv4910_val = Inv4910
	   /\ Inv4912_val = Inv4912
	   /\ Inv4914_val = Inv4914
	   /\ Inv4919_val = Inv4919
	   /\ Inv4922_val = Inv4922
	   /\ Inv4924_val = Inv4924
	   /\ Inv4925_val = Inv4925
	   /\ Inv4929_val = Inv4929
	   /\ Inv4933_val = Inv4933
	   /\ Inv4935_val = Inv4935
	   /\ Inv4937_val = Inv4937
	   /\ Inv4939_val = Inv4939
	   /\ Inv4940_val = Inv4940
	   /\ Inv4941_val = Inv4941
	   /\ Inv4942_val = Inv4942
	   /\ Inv4943_val = Inv4943
	   /\ Inv4945_val = Inv4945
	   /\ Inv4946_val = Inv4946
	   /\ Inv4949_val = Inv4949
	   /\ Inv4950_val = Inv4950
	   /\ Inv4951_val = Inv4951
	   /\ Inv4955_val = Inv4955
	   /\ Inv4956_val = Inv4956
	   /\ Inv4957_val = Inv4957
	   /\ Inv4958_val = Inv4958
	   /\ Inv4959_val = Inv4959
	   /\ Inv4960_val = Inv4960
	   /\ Inv4961_val = Inv4961
	   /\ Inv4962_val = Inv4962
	   /\ Inv4963_val = Inv4963
	   /\ Inv4964_val = Inv4964
	   /\ Inv4965_val = Inv4965
	   /\ Inv4966_val = Inv4966
	   /\ Inv4967_val = Inv4967
	   /\ Inv4968_val = Inv4968
	   /\ Inv4969_val = Inv4969
	   /\ Inv4970_val = Inv4970
	   /\ Inv4971_val = Inv4971
	   /\ Inv4972_val = Inv4972
	   /\ Inv4973_val = Inv4973
	   /\ Inv4974_val = Inv4974
	   /\ Inv4975_val = Inv4975
	   /\ Inv4976_val = Inv4976
	   /\ Inv4977_val = Inv4977
	   /\ Inv4978_val = Inv4978
	   /\ Inv4979_val = Inv4979
	   /\ Inv4980_val = Inv4980
	   /\ Inv4981_val = Inv4981
	   /\ Inv4982_val = Inv4982
	   /\ Inv4983_val = Inv4983
	   /\ Inv4984_val = Inv4984
	   /\ Inv4985_val = Inv4985
	   /\ Inv4986_val = Inv4986
	   /\ Inv4987_val = Inv4987
	   /\ Inv4988_val = Inv4988
	   /\ Inv4989_val = Inv4989
	   /\ Inv4990_val = Inv4990
	   /\ Inv4991_val = Inv4991
	   /\ Inv4992_val = Inv4992
	   /\ Inv4993_val = Inv4993
	   /\ Inv4994_val = Inv4994
	   /\ Inv4995_val = Inv4995
	   /\ Inv4998_val = Inv4998
	   /\ Inv4999_val = Inv4999
	   /\ Inv5_val = Inv5
	   /\ Inv500_val = Inv500
	   /\ Inv5001_val = Inv5001
	   /\ Inv5002_val = Inv5002
	   /\ Inv5003_val = Inv5003
	   /\ Inv5007_val = Inv5007
	   /\ Inv5008_val = Inv5008
	   /\ Inv5009_val = Inv5009
	   /\ Inv5010_val = Inv5010
	   /\ Inv5011_val = Inv5011
	   /\ Inv5014_val = Inv5014
	   /\ Inv5015_val = Inv5015
	   /\ Inv5016_val = Inv5016
	   /\ Inv5017_val = Inv5017
	   /\ Inv5018_val = Inv5018
	   /\ Inv5019_val = Inv5019
	   /\ Inv5020_val = Inv5020
	   /\ Inv5021_val = Inv5021
	   /\ Inv5022_val = Inv5022
	   /\ Inv5023_val = Inv5023
	   /\ Inv5024_val = Inv5024
	   /\ Inv5025_val = Inv5025
	   /\ Inv5026_val = Inv5026
	   /\ Inv5027_val = Inv5027
	   /\ Inv5028_val = Inv5028
	   /\ Inv5029_val = Inv5029
	   /\ Inv5030_val = Inv5030
	   /\ Inv5031_val = Inv5031
	   /\ Inv5034_val = Inv5034
	   /\ Inv5035_val = Inv5035
	   /\ Inv5036_val = Inv5036
	   /\ Inv5037_val = Inv5037
	   /\ Inv5040_val = Inv5040
	   /\ Inv5041_val = Inv5041
	   /\ Inv5042_val = Inv5042
	   /\ Inv5043_val = Inv5043
	   /\ Inv5049_val = Inv5049
	   /\ Inv505_val = Inv505
	   /\ Inv5050_val = Inv5050
	   /\ Inv5051_val = Inv5051
	   /\ Inv5052_val = Inv5052
	   /\ Inv5054_val = Inv5054
	   /\ Inv5055_val = Inv5055
	   /\ Inv5056_val = Inv5056
	   /\ Inv5058_val = Inv5058
	   /\ Inv5059_val = Inv5059
	   /\ Inv506_val = Inv506
	   /\ Inv5060_val = Inv5060
	   /\ Inv5061_val = Inv5061
	   /\ Inv5062_val = Inv5062
	   /\ Inv5063_val = Inv5063
	   /\ Inv5064_val = Inv5064
	   /\ Inv5065_val = Inv5065
	   /\ Inv5066_val = Inv5066
	   /\ Inv5067_val = Inv5067
	   /\ Inv5068_val = Inv5068
	   /\ Inv5069_val = Inv5069
	   /\ Inv5070_val = Inv5070
	   /\ Inv5071_val = Inv5071
	   /\ Inv5072_val = Inv5072
	   /\ Inv5073_val = Inv5073
	   /\ Inv5074_val = Inv5074
	   /\ Inv5075_val = Inv5075
	   /\ Inv5076_val = Inv5076
	   /\ Inv5077_val = Inv5077
	   /\ Inv5078_val = Inv5078
	   /\ Inv5079_val = Inv5079
	   /\ Inv5080_val = Inv5080
	   /\ Inv5081_val = Inv5081
	   /\ Inv5082_val = Inv5082
	   /\ Inv5083_val = Inv5083
	   /\ Inv5084_val = Inv5084
	   /\ Inv5085_val = Inv5085
	   /\ Inv5086_val = Inv5086
	   /\ Inv5087_val = Inv5087
	   /\ Inv5088_val = Inv5088
	   /\ Inv5089_val = Inv5089
	   /\ Inv5090_val = Inv5090
	   /\ Inv5091_val = Inv5091
	   /\ Inv5092_val = Inv5092
	   /\ Inv5093_val = Inv5093
	   /\ Inv5094_val = Inv5094
	   /\ Inv5095_val = Inv5095
	   /\ Inv5099_val = Inv5099
	   /\ Inv5101_val = Inv5101
	   /\ Inv5102_val = Inv5102
	   /\ Inv5103_val = Inv5103
	   /\ Inv5104_val = Inv5104
	   /\ Inv5105_val = Inv5105
	   /\ Inv5106_val = Inv5106
	   /\ Inv5107_val = Inv5107
	   /\ Inv5108_val = Inv5108
	   /\ Inv5109_val = Inv5109
	   /\ Inv511_val = Inv511
	   /\ Inv5110_val = Inv5110
	   /\ Inv5111_val = Inv5111
	   /\ Inv5112_val = Inv5112
	   /\ Inv5113_val = Inv5113
	   /\ Inv5114_val = Inv5114
	   /\ Inv5115_val = Inv5115
	   /\ Inv512_val = Inv512
	   /\ Inv5122_val = Inv5122
	   /\ Inv5123_val = Inv5123
	   /\ Inv5124_val = Inv5124
	   /\ Inv5127_val = Inv5127
	   /\ Inv5128_val = Inv5128
	   /\ Inv5130_val = Inv5130
	   /\ Inv5135_val = Inv5135
	   /\ Inv5138_val = Inv5138
	   /\ Inv5139_val = Inv5139
	   /\ Inv514_val = Inv514
	   /\ Inv5141_val = Inv5141
	   /\ Inv5142_val = Inv5142
	   /\ Inv5146_val = Inv5146
	   /\ Inv515_val = Inv515
	   /\ Inv5158_val = Inv5158
	   /\ Inv5159_val = Inv5159
	   /\ Inv5162_val = Inv5162
	   /\ Inv5163_val = Inv5163
	   /\ Inv5164_val = Inv5164
	   /\ Inv5165_val = Inv5165
	   /\ Inv5166_val = Inv5166
	   /\ Inv5167_val = Inv5167
	   /\ Inv5168_val = Inv5168
	   /\ Inv5173_val = Inv5173
	   /\ Inv5175_val = Inv5175
	   /\ Inv5176_val = Inv5176
	   /\ Inv5178_val = Inv5178
	   /\ Inv5180_val = Inv5180
	   /\ Inv5184_val = Inv5184
	   /\ Inv5188_val = Inv5188
	   /\ Inv5190_val = Inv5190
	   /\ Inv5191_val = Inv5191
	   /\ Inv5192_val = Inv5192
	   /\ Inv5193_val = Inv5193
	   /\ Inv5196_val = Inv5196
	   /\ Inv5197_val = Inv5197
	   /\ Inv52_val = Inv52
	   /\ Inv5200_val = Inv5200
	   /\ Inv5202_val = Inv5202
	   /\ Inv5203_val = Inv5203
	   /\ Inv5204_val = Inv5204
	   /\ Inv5205_val = Inv5205
	   /\ Inv5207_val = Inv5207
	   /\ Inv5209_val = Inv5209
	   /\ Inv5210_val = Inv5210
	   /\ Inv5212_val = Inv5212
	   /\ Inv5213_val = Inv5213
	   /\ Inv5215_val = Inv5215
	   /\ Inv5217_val = Inv5217
	   /\ Inv5219_val = Inv5219
	   /\ Inv522_val = Inv522
	   /\ Inv5222_val = Inv5222
	   /\ Inv5225_val = Inv5225
	   /\ Inv5228_val = Inv5228
	   /\ Inv5229_val = Inv5229
	   /\ Inv523_val = Inv523
	   /\ Inv5230_val = Inv5230
	   /\ Inv5231_val = Inv5231
	   /\ Inv5236_val = Inv5236
	   /\ Inv5237_val = Inv5237
	   /\ Inv5238_val = Inv5238
	   /\ Inv5239_val = Inv5239
	   /\ Inv524_val = Inv524
	   /\ Inv5241_val = Inv5241
	   /\ Inv5242_val = Inv5242
	   /\ Inv5243_val = Inv5243
	   /\ Inv5244_val = Inv5244
	   /\ Inv5245_val = Inv5245
	   /\ Inv5248_val = Inv5248
	   /\ Inv5249_val = Inv5249
	   /\ Inv5251_val = Inv5251
	   /\ Inv5254_val = Inv5254
	   /\ Inv5256_val = Inv5256
	   /\ Inv5257_val = Inv5257
	   /\ Inv5258_val = Inv5258
	   /\ Inv5259_val = Inv5259
	   /\ Inv5260_val = Inv5260
	   /\ Inv5261_val = Inv5261
	   /\ Inv5262_val = Inv5262
	   /\ Inv5263_val = Inv5263
	   /\ Inv5264_val = Inv5264
	   /\ Inv5265_val = Inv5265
	   /\ Inv5266_val = Inv5266
	   /\ Inv5267_val = Inv5267
	   /\ Inv5268_val = Inv5268
	   /\ Inv5269_val = Inv5269
	   /\ Inv5270_val = Inv5270
	   /\ Inv5271_val = Inv5271
	   /\ Inv5272_val = Inv5272
	   /\ Inv5273_val = Inv5273
	   /\ Inv5274_val = Inv5274
	   /\ Inv5275_val = Inv5275
	   /\ Inv5276_val = Inv5276
	   /\ Inv5277_val = Inv5277
	   /\ Inv5278_val = Inv5278
	   /\ Inv5279_val = Inv5279
	   /\ Inv5280_val = Inv5280
	   /\ Inv5281_val = Inv5281
	   /\ Inv5282_val = Inv5282
	   /\ Inv5283_val = Inv5283
	   /\ Inv5284_val = Inv5284
	   /\ Inv5285_val = Inv5285
	   /\ Inv5286_val = Inv5286
	   /\ Inv5287_val = Inv5287
	   /\ Inv5288_val = Inv5288
	   /\ Inv5289_val = Inv5289
	   /\ Inv5290_val = Inv5290
	   /\ Inv5291_val = Inv5291
	   /\ Inv5292_val = Inv5292
	   /\ Inv5293_val = Inv5293
	   /\ Inv5294_val = Inv5294
	   /\ Inv5295_val = Inv5295
	   /\ Inv5296_val = Inv5296
	   /\ Inv5297_val = Inv5297
	   /\ Inv5298_val = Inv5298
	   /\ Inv5299_val = Inv5299
	   /\ Inv530_val = Inv530
	   /\ Inv5300_val = Inv5300
	   /\ Inv5304_val = Inv5304
	   /\ Inv5305_val = Inv5305
	   /\ Inv5306_val = Inv5306
	   /\ Inv5308_val = Inv5308
	   /\ Inv5312_val = Inv5312
	   /\ Inv5313_val = Inv5313
	   /\ Inv5314_val = Inv5314
	   /\ Inv5315_val = Inv5315
	   /\ Inv5316_val = Inv5316
	   /\ Inv5317_val = Inv5317
	   /\ Inv5318_val = Inv5318
	   /\ Inv5319_val = Inv5319
	   /\ Inv5320_val = Inv5320
	   /\ Inv5321_val = Inv5321
	   /\ Inv5322_val = Inv5322
	   /\ Inv5323_val = Inv5323
	   /\ Inv5324_val = Inv5324
	   /\ Inv5325_val = Inv5325
	   /\ Inv5326_val = Inv5326
	   /\ Inv5327_val = Inv5327
	   /\ Inv5328_val = Inv5328
	   /\ Inv5329_val = Inv5329
	   /\ Inv5330_val = Inv5330
	   /\ Inv5331_val = Inv5331
	   /\ Inv5332_val = Inv5332
	   /\ Inv5333_val = Inv5333
	   /\ Inv5334_val = Inv5334
	   /\ Inv5336_val = Inv5336
	   /\ Inv5338_val = Inv5338
	   /\ Inv5339_val = Inv5339
	   /\ Inv5341_val = Inv5341
	   /\ Inv5343_val = Inv5343
	   /\ Inv5344_val = Inv5344
	   /\ Inv5346_val = Inv5346
	   /\ Inv5347_val = Inv5347
	   /\ Inv5349_val = Inv5349
	   /\ Inv5350_val = Inv5350
	   /\ Inv5351_val = Inv5351
	   /\ Inv5352_val = Inv5352
	   /\ Inv5353_val = Inv5353
	   /\ Inv5354_val = Inv5354
	   /\ Inv5355_val = Inv5355
	   /\ Inv5356_val = Inv5356
	   /\ Inv5357_val = Inv5357
	   /\ Inv5358_val = Inv5358
	   /\ Inv5359_val = Inv5359
	   /\ Inv536_val = Inv536
	   /\ Inv5360_val = Inv5360
	   /\ Inv5361_val = Inv5361
	   /\ Inv5362_val = Inv5362
	   /\ Inv5363_val = Inv5363
	   /\ Inv5364_val = Inv5364
	   /\ Inv5365_val = Inv5365
	   /\ Inv5366_val = Inv5366
	   /\ Inv5367_val = Inv5367
	   /\ Inv5368_val = Inv5368
	   /\ Inv5369_val = Inv5369
	   /\ Inv537_val = Inv537
	   /\ Inv5370_val = Inv5370
	   /\ Inv5371_val = Inv5371
	   /\ Inv5372_val = Inv5372
	   /\ Inv5373_val = Inv5373
	   /\ Inv5374_val = Inv5374
	   /\ Inv5375_val = Inv5375
	   /\ Inv5376_val = Inv5376
	   /\ Inv5377_val = Inv5377
	   /\ Inv5378_val = Inv5378
	   /\ Inv5379_val = Inv5379
	   /\ Inv5381_val = Inv5381
	   /\ Inv5383_val = Inv5383
	   /\ Inv5384_val = Inv5384
	   /\ Inv5386_val = Inv5386
	   /\ Inv5387_val = Inv5387
	   /\ Inv5388_val = Inv5388
	   /\ Inv5389_val = Inv5389
	   /\ Inv5390_val = Inv5390
	   /\ Inv5391_val = Inv5391
	   /\ Inv5392_val = Inv5392
	   /\ Inv5393_val = Inv5393
	   /\ Inv5394_val = Inv5394
	   /\ Inv5395_val = Inv5395
	   /\ Inv5396_val = Inv5396
	   /\ Inv5397_val = Inv5397
	   /\ Inv540_val = Inv540
	   /\ Inv5402_val = Inv5402
	   /\ Inv5404_val = Inv5404
	   /\ Inv5405_val = Inv5405
	   /\ Inv541_val = Inv541
	   /\ Inv5415_val = Inv5415
	   /\ Inv5416_val = Inv5416
	   /\ Inv542_val = Inv542
	   /\ Inv5422_val = Inv5422
	   /\ Inv5423_val = Inv5423
	   /\ Inv5428_val = Inv5428
	   /\ Inv5433_val = Inv5433
	   /\ Inv5434_val = Inv5434
	   /\ Inv5435_val = Inv5435
	   /\ Inv5437_val = Inv5437
	   /\ Inv5438_val = Inv5438
	   /\ Inv5440_val = Inv5440
	   /\ Inv5442_val = Inv5442
	   /\ Inv5443_val = Inv5443
	   /\ Inv5444_val = Inv5444
	   /\ Inv5447_val = Inv5447
	   /\ Inv5448_val = Inv5448
	   /\ Inv5452_val = Inv5452
	   /\ Inv5454_val = Inv5454
	   /\ Inv5456_val = Inv5456
	   /\ Inv5457_val = Inv5457
	   /\ Inv5458_val = Inv5458
	   /\ Inv5459_val = Inv5459
	   /\ Inv5460_val = Inv5460
	   /\ Inv5461_val = Inv5461
	   /\ Inv5470_val = Inv5470
	   /\ Inv5475_val = Inv5475
	   /\ Inv5479_val = Inv5479
	   /\ Inv548_val = Inv548
	   /\ Inv5480_val = Inv5480
	   /\ Inv5481_val = Inv5481
	   /\ Inv5482_val = Inv5482
	   /\ Inv5483_val = Inv5483
	   /\ Inv5486_val = Inv5486
	   /\ Inv549_val = Inv549
	   /\ Inv5494_val = Inv5494
	   /\ Inv5498_val = Inv5498
	   /\ Inv5499_val = Inv5499
	   /\ Inv550_val = Inv550
	   /\ Inv5501_val = Inv5501
	   /\ Inv5504_val = Inv5504
	   /\ Inv5506_val = Inv5506
	   /\ Inv5507_val = Inv5507
	   /\ Inv5508_val = Inv5508
	   /\ Inv5511_val = Inv5511
	   /\ Inv5512_val = Inv5512
	   /\ Inv5520_val = Inv5520
	   /\ Inv5521_val = Inv5521
	   /\ Inv5522_val = Inv5522
	   /\ Inv5523_val = Inv5523
	   /\ Inv5524_val = Inv5524
	   /\ Inv5525_val = Inv5525
	   /\ Inv5526_val = Inv5526
	   /\ Inv5527_val = Inv5527
	   /\ Inv5528_val = Inv5528
	   /\ Inv5529_val = Inv5529
	   /\ Inv5530_val = Inv5530
	   /\ Inv5531_val = Inv5531
	   /\ Inv5532_val = Inv5532
	   /\ Inv5533_val = Inv5533
	   /\ Inv5534_val = Inv5534
	   /\ Inv5535_val = Inv5535
	   /\ Inv5536_val = Inv5536
	   /\ Inv5537_val = Inv5537
	   /\ Inv5538_val = Inv5538
	   /\ Inv5539_val = Inv5539
	   /\ Inv554_val = Inv554
	   /\ Inv5540_val = Inv5540
	   /\ Inv5541_val = Inv5541
	   /\ Inv5542_val = Inv5542
	   /\ Inv5543_val = Inv5543
	   /\ Inv5544_val = Inv5544
	   /\ Inv5545_val = Inv5545
	   /\ Inv5546_val = Inv5546
	   /\ Inv5549_val = Inv5549
	   /\ Inv5551_val = Inv5551
	   /\ Inv5552_val = Inv5552
	   /\ Inv5553_val = Inv5553
	   /\ Inv5554_val = Inv5554
	   /\ Inv5556_val = Inv5556
	   /\ Inv5557_val = Inv5557
	   /\ Inv5558_val = Inv5558
	   /\ Inv556_val = Inv556
	   /\ Inv5560_val = Inv5560
	   /\ Inv5562_val = Inv5562
	   /\ Inv5563_val = Inv5563
	   /\ Inv5564_val = Inv5564
	   /\ Inv5565_val = Inv5565
	   /\ Inv5566_val = Inv5566
	   /\ Inv5567_val = Inv5567
	   /\ Inv5568_val = Inv5568
	   /\ Inv5569_val = Inv5569
	   /\ Inv5570_val = Inv5570
	   /\ Inv5571_val = Inv5571
	   /\ Inv5572_val = Inv5572
	   /\ Inv5573_val = Inv5573
	   /\ Inv5574_val = Inv5574
	   /\ Inv5575_val = Inv5575
	   /\ Inv5577_val = Inv5577
	   /\ Inv558_val = Inv558
	   /\ Inv5580_val = Inv5580
	   /\ Inv5582_val = Inv5582
	   /\ Inv5583_val = Inv5583
	   /\ Inv5584_val = Inv5584
	   /\ Inv5591_val = Inv5591
	   /\ Inv5592_val = Inv5592
	   /\ Inv5594_val = Inv5594
	   /\ Inv5595_val = Inv5595
	   /\ Inv5596_val = Inv5596
	   /\ Inv5597_val = Inv5597
	   /\ Inv5598_val = Inv5598
	   /\ Inv5599_val = Inv5599
	   /\ Inv56_val = Inv56
	   /\ Inv5600_val = Inv5600
	   /\ Inv5601_val = Inv5601
	   /\ Inv5602_val = Inv5602
	   /\ Inv5603_val = Inv5603
	   /\ Inv5604_val = Inv5604

CTICheckInit ==
    /\ kCTIs
    /\ InvVals
    /\ Inv4612_1_0
    /\ Inv1170_1_1
    /\ Inv4101_1_2
    /\ Inv5926_1_3
    /\ Inv4154_1_0
    /\ Inv2501_1_1
    /\ Inv6101_1_2
    /\ Inv6114_1_3
    /\ Inv12388_2_4

CTICheckNext ==
    /\ NextUnchanged
    /\ UNCHANGED ctiId
    /\ UNCHANGED Inv4149_val
    /\ UNCHANGED Inv415_val
    /\ UNCHANGED Inv4150_val
    /\ UNCHANGED Inv4151_val
    /\ UNCHANGED Inv4152_val
    /\ UNCHANGED Inv4153_val
    /\ UNCHANGED Inv4154_val
    /\ UNCHANGED Inv4155_val
    /\ UNCHANGED Inv4156_val
    /\ UNCHANGED Inv416_val
    /\ UNCHANGED Inv4160_val
    /\ UNCHANGED Inv4161_val
    /\ UNCHANGED Inv4163_val
    /\ UNCHANGED Inv4164_val
    /\ UNCHANGED Inv4166_val
    /\ UNCHANGED Inv4170_val
    /\ UNCHANGED Inv4171_val
    /\ UNCHANGED Inv4172_val
    /\ UNCHANGED Inv4173_val
    /\ UNCHANGED Inv4174_val
    /\ UNCHANGED Inv4175_val
    /\ UNCHANGED Inv4176_val
    /\ UNCHANGED Inv4177_val
    /\ UNCHANGED Inv4178_val
    /\ UNCHANGED Inv4179_val
    /\ UNCHANGED Inv4180_val
    /\ UNCHANGED Inv4181_val
    /\ UNCHANGED Inv4182_val
    /\ UNCHANGED Inv4183_val
    /\ UNCHANGED Inv4184_val
    /\ UNCHANGED Inv4185_val
    /\ UNCHANGED Inv4186_val
    /\ UNCHANGED Inv4187_val
    /\ UNCHANGED Inv4188_val
    /\ UNCHANGED Inv4189_val
    /\ UNCHANGED Inv4190_val
    /\ UNCHANGED Inv4191_val
    /\ UNCHANGED Inv4192_val
    /\ UNCHANGED Inv4193_val
    /\ UNCHANGED Inv4194_val
    /\ UNCHANGED Inv4195_val
    /\ UNCHANGED Inv4196_val
    /\ UNCHANGED Inv4197_val
    /\ UNCHANGED Inv4198_val
    /\ UNCHANGED Inv4199_val
    /\ UNCHANGED Inv4200_val
    /\ UNCHANGED Inv4201_val
    /\ UNCHANGED Inv4202_val
    /\ UNCHANGED Inv4203_val
    /\ UNCHANGED Inv4204_val
    /\ UNCHANGED Inv4205_val
    /\ UNCHANGED Inv4206_val
    /\ UNCHANGED Inv4207_val
    /\ UNCHANGED Inv4208_val
    /\ UNCHANGED Inv4209_val
    /\ UNCHANGED Inv421_val
    /\ UNCHANGED Inv4210_val
    /\ UNCHANGED Inv4211_val
    /\ UNCHANGED Inv4218_val
    /\ UNCHANGED Inv4221_val
    /\ UNCHANGED Inv4222_val
    /\ UNCHANGED Inv4223_val
    /\ UNCHANGED Inv4224_val
    /\ UNCHANGED Inv4225_val
    /\ UNCHANGED Inv4226_val
    /\ UNCHANGED Inv4227_val
    /\ UNCHANGED Inv4228_val
    /\ UNCHANGED Inv4229_val
    /\ UNCHANGED Inv4230_val
    /\ UNCHANGED Inv4231_val
    /\ UNCHANGED Inv4232_val
    /\ UNCHANGED Inv4233_val
    /\ UNCHANGED Inv4234_val
    /\ UNCHANGED Inv4237_val
    /\ UNCHANGED Inv4238_val
    /\ UNCHANGED Inv4239_val
    /\ UNCHANGED Inv424_val
    /\ UNCHANGED Inv4240_val
    /\ UNCHANGED Inv4241_val
    /\ UNCHANGED Inv4244_val
    /\ UNCHANGED Inv4247_val
    /\ UNCHANGED Inv4249_val
    /\ UNCHANGED Inv4250_val
    /\ UNCHANGED Inv4251_val
    /\ UNCHANGED Inv4255_val
    /\ UNCHANGED Inv4270_val
    /\ UNCHANGED Inv4273_val
    /\ UNCHANGED Inv4275_val
    /\ UNCHANGED Inv4277_val
    /\ UNCHANGED Inv4278_val
    /\ UNCHANGED Inv428_val
    /\ UNCHANGED Inv4280_val
    /\ UNCHANGED Inv4281_val
    /\ UNCHANGED Inv4288_val
    /\ UNCHANGED Inv4290_val
    /\ UNCHANGED Inv4291_val
    /\ UNCHANGED Inv4292_val
    /\ UNCHANGED Inv4302_val
    /\ UNCHANGED Inv4303_val
    /\ UNCHANGED Inv4308_val
    /\ UNCHANGED Inv4311_val
    /\ UNCHANGED Inv4312_val
    /\ UNCHANGED Inv4314_val
    /\ UNCHANGED Inv4318_val
    /\ UNCHANGED Inv4319_val
    /\ UNCHANGED Inv432_val
    /\ UNCHANGED Inv4321_val
    /\ UNCHANGED Inv4323_val
    /\ UNCHANGED Inv4324_val
    /\ UNCHANGED Inv4329_val
    /\ UNCHANGED Inv433_val
    /\ UNCHANGED Inv4330_val
    /\ UNCHANGED Inv4331_val
    /\ UNCHANGED Inv4332_val
    /\ UNCHANGED Inv4333_val
    /\ UNCHANGED Inv434_val
    /\ UNCHANGED Inv4340_val
    /\ UNCHANGED Inv4343_val
    /\ UNCHANGED Inv4345_val
    /\ UNCHANGED Inv4346_val
    /\ UNCHANGED Inv4347_val
    /\ UNCHANGED Inv4348_val
    /\ UNCHANGED Inv4352_val
    /\ UNCHANGED Inv4353_val
    /\ UNCHANGED Inv4354_val
    /\ UNCHANGED Inv4357_val
    /\ UNCHANGED Inv4358_val
    /\ UNCHANGED Inv4359_val
    /\ UNCHANGED Inv4360_val
    /\ UNCHANGED Inv4361_val
    /\ UNCHANGED Inv4364_val
    /\ UNCHANGED Inv4366_val
    /\ UNCHANGED Inv437_val
    /\ UNCHANGED Inv4370_val
    /\ UNCHANGED Inv4371_val
    /\ UNCHANGED Inv4372_val
    /\ UNCHANGED Inv4373_val
    /\ UNCHANGED Inv4375_val
    /\ UNCHANGED Inv4376_val
    /\ UNCHANGED Inv4378_val
    /\ UNCHANGED Inv4379_val
    /\ UNCHANGED Inv438_val
    /\ UNCHANGED Inv4380_val
    /\ UNCHANGED Inv4381_val
    /\ UNCHANGED Inv4382_val
    /\ UNCHANGED Inv4383_val
    /\ UNCHANGED Inv4384_val
    /\ UNCHANGED Inv4385_val
    /\ UNCHANGED Inv4386_val
    /\ UNCHANGED Inv4387_val
    /\ UNCHANGED Inv4388_val
    /\ UNCHANGED Inv4389_val
    /\ UNCHANGED Inv4390_val
    /\ UNCHANGED Inv4391_val
    /\ UNCHANGED Inv4392_val
    /\ UNCHANGED Inv4393_val
    /\ UNCHANGED Inv4394_val
    /\ UNCHANGED Inv4395_val
    /\ UNCHANGED Inv4396_val
    /\ UNCHANGED Inv4397_val
    /\ UNCHANGED Inv4398_val
    /\ UNCHANGED Inv4399_val
    /\ UNCHANGED Inv440_val
    /\ UNCHANGED Inv4400_val
    /\ UNCHANGED Inv4401_val
    /\ UNCHANGED Inv4402_val
    /\ UNCHANGED Inv4403_val
    /\ UNCHANGED Inv4404_val
    /\ UNCHANGED Inv4405_val
    /\ UNCHANGED Inv4406_val
    /\ UNCHANGED Inv4407_val
    /\ UNCHANGED Inv4408_val
    /\ UNCHANGED Inv4409_val
    /\ UNCHANGED Inv4410_val
    /\ UNCHANGED Inv4411_val
    /\ UNCHANGED Inv4412_val
    /\ UNCHANGED Inv4414_val
    /\ UNCHANGED Inv4415_val
    /\ UNCHANGED Inv4416_val
    /\ UNCHANGED Inv4417_val
    /\ UNCHANGED Inv4418_val
    /\ UNCHANGED Inv4420_val
    /\ UNCHANGED Inv4421_val
    /\ UNCHANGED Inv4424_val
    /\ UNCHANGED Inv4425_val
    /\ UNCHANGED Inv4426_val
    /\ UNCHANGED Inv4427_val
    /\ UNCHANGED Inv4428_val
    /\ UNCHANGED Inv4429_val
    /\ UNCHANGED Inv4430_val
    /\ UNCHANGED Inv4431_val
    /\ UNCHANGED Inv4432_val
    /\ UNCHANGED Inv4433_val
    /\ UNCHANGED Inv4434_val
    /\ UNCHANGED Inv4435_val
    /\ UNCHANGED Inv4436_val
    /\ UNCHANGED Inv4437_val
    /\ UNCHANGED Inv4438_val
    /\ UNCHANGED Inv4440_val
    /\ UNCHANGED Inv4442_val
    /\ UNCHANGED Inv4444_val
    /\ UNCHANGED Inv4445_val
    /\ UNCHANGED Inv4446_val
    /\ UNCHANGED Inv4448_val
    /\ UNCHANGED Inv4449_val
    /\ UNCHANGED Inv445_val
    /\ UNCHANGED Inv4450_val
    /\ UNCHANGED Inv4451_val
    /\ UNCHANGED Inv4452_val
    /\ UNCHANGED Inv4453_val
    /\ UNCHANGED Inv4455_val
    /\ UNCHANGED Inv4456_val
    /\ UNCHANGED Inv4458_val
    /\ UNCHANGED Inv4463_val
    /\ UNCHANGED Inv4464_val
    /\ UNCHANGED Inv4465_val
    /\ UNCHANGED Inv4466_val
    /\ UNCHANGED Inv4467_val
    /\ UNCHANGED Inv4468_val
    /\ UNCHANGED Inv4469_val
    /\ UNCHANGED Inv4470_val
    /\ UNCHANGED Inv4471_val
    /\ UNCHANGED Inv4472_val
    /\ UNCHANGED Inv4473_val
    /\ UNCHANGED Inv4474_val
    /\ UNCHANGED Inv4475_val
    /\ UNCHANGED Inv4476_val
    /\ UNCHANGED Inv4477_val
    /\ UNCHANGED Inv4478_val
    /\ UNCHANGED Inv4479_val
    /\ UNCHANGED Inv448_val
    /\ UNCHANGED Inv4480_val
    /\ UNCHANGED Inv4481_val
    /\ UNCHANGED Inv4482_val
    /\ UNCHANGED Inv4483_val
    /\ UNCHANGED Inv4484_val
    /\ UNCHANGED Inv4485_val
    /\ UNCHANGED Inv4488_val
    /\ UNCHANGED Inv4489_val
    /\ UNCHANGED Inv4490_val
    /\ UNCHANGED Inv4491_val
    /\ UNCHANGED Inv4492_val
    /\ UNCHANGED Inv4493_val
    /\ UNCHANGED Inv4494_val
    /\ UNCHANGED Inv4495_val
    /\ UNCHANGED Inv4496_val
    /\ UNCHANGED Inv4497_val
    /\ UNCHANGED Inv4498_val
    /\ UNCHANGED Inv4499_val
    /\ UNCHANGED Inv4501_val
    /\ UNCHANGED Inv4502_val
    /\ UNCHANGED Inv4503_val
    /\ UNCHANGED Inv4504_val
    /\ UNCHANGED Inv4505_val
    /\ UNCHANGED Inv4506_val
    /\ UNCHANGED Inv4507_val
    /\ UNCHANGED Inv4508_val
    /\ UNCHANGED Inv4509_val
    /\ UNCHANGED Inv4513_val
    /\ UNCHANGED Inv4516_val
    /\ UNCHANGED Inv4518_val
    /\ UNCHANGED Inv4519_val
    /\ UNCHANGED Inv4520_val
    /\ UNCHANGED Inv4521_val
    /\ UNCHANGED Inv4522_val
    /\ UNCHANGED Inv4525_val
    /\ UNCHANGED Inv4527_val
    /\ UNCHANGED Inv4535_val
    /\ UNCHANGED Inv4537_val
    /\ UNCHANGED Inv4538_val
    /\ UNCHANGED Inv4544_val
    /\ UNCHANGED Inv4547_val
    /\ UNCHANGED Inv4548_val
    /\ UNCHANGED Inv455_val
    /\ UNCHANGED Inv4551_val
    /\ UNCHANGED Inv4553_val
    /\ UNCHANGED Inv4559_val
    /\ UNCHANGED Inv4560_val
    /\ UNCHANGED Inv4561_val
    /\ UNCHANGED Inv4562_val
    /\ UNCHANGED Inv4567_val
    /\ UNCHANGED Inv4571_val
    /\ UNCHANGED Inv4572_val
    /\ UNCHANGED Inv4577_val
    /\ UNCHANGED Inv4579_val
    /\ UNCHANGED Inv458_val
    /\ UNCHANGED Inv4581_val
    /\ UNCHANGED Inv4583_val
    /\ UNCHANGED Inv4586_val
    /\ UNCHANGED Inv4587_val
    /\ UNCHANGED Inv4590_val
    /\ UNCHANGED Inv4592_val
    /\ UNCHANGED Inv4593_val
    /\ UNCHANGED Inv4594_val
    /\ UNCHANGED Inv4596_val
    /\ UNCHANGED Inv4597_val
    /\ UNCHANGED Inv4598_val
    /\ UNCHANGED Inv46_val
    /\ UNCHANGED Inv4602_val
    /\ UNCHANGED Inv4604_val
    /\ UNCHANGED Inv4609_val
    /\ UNCHANGED Inv4610_val
    /\ UNCHANGED Inv4611_val
    /\ UNCHANGED Inv4619_val
    /\ UNCHANGED Inv4620_val
    /\ UNCHANGED Inv4625_val
    /\ UNCHANGED Inv4626_val
    /\ UNCHANGED Inv4627_val
    /\ UNCHANGED Inv4629_val
    /\ UNCHANGED Inv4631_val
    /\ UNCHANGED Inv4633_val
    /\ UNCHANGED Inv4634_val
    /\ UNCHANGED Inv4636_val
    /\ UNCHANGED Inv4638_val
    /\ UNCHANGED Inv4639_val
    /\ UNCHANGED Inv4641_val
    /\ UNCHANGED Inv4644_val
    /\ UNCHANGED Inv4645_val
    /\ UNCHANGED Inv4647_val
    /\ UNCHANGED Inv4648_val
    /\ UNCHANGED Inv4651_val
    /\ UNCHANGED Inv4652_val
    /\ UNCHANGED Inv4653_val
    /\ UNCHANGED Inv4655_val
    /\ UNCHANGED Inv4656_val
    /\ UNCHANGED Inv4657_val
    /\ UNCHANGED Inv4658_val
    /\ UNCHANGED Inv4659_val
    /\ UNCHANGED Inv4660_val
    /\ UNCHANGED Inv4661_val
    /\ UNCHANGED Inv4662_val
    /\ UNCHANGED Inv4663_val
    /\ UNCHANGED Inv4664_val
    /\ UNCHANGED Inv4665_val
    /\ UNCHANGED Inv4666_val
    /\ UNCHANGED Inv4667_val
    /\ UNCHANGED Inv4668_val
    /\ UNCHANGED Inv4669_val
    /\ UNCHANGED Inv4670_val
    /\ UNCHANGED Inv4671_val
    /\ UNCHANGED Inv4672_val
    /\ UNCHANGED Inv4673_val
    /\ UNCHANGED Inv4674_val
    /\ UNCHANGED Inv4675_val
    /\ UNCHANGED Inv4676_val
    /\ UNCHANGED Inv4677_val
    /\ UNCHANGED Inv4678_val
    /\ UNCHANGED Inv4679_val
    /\ UNCHANGED Inv468_val
    /\ UNCHANGED Inv4680_val
    /\ UNCHANGED Inv4681_val
    /\ UNCHANGED Inv4683_val
    /\ UNCHANGED Inv4686_val
    /\ UNCHANGED Inv4687_val
    /\ UNCHANGED Inv4688_val
    /\ UNCHANGED Inv4689_val
    /\ UNCHANGED Inv4692_val
    /\ UNCHANGED Inv4693_val
    /\ UNCHANGED Inv4695_val
    /\ UNCHANGED Inv4696_val
    /\ UNCHANGED Inv4697_val
    /\ UNCHANGED Inv4698_val
    /\ UNCHANGED Inv4699_val
    /\ UNCHANGED Inv47_val
    /\ UNCHANGED Inv4702_val
    /\ UNCHANGED Inv4704_val
    /\ UNCHANGED Inv4705_val
    /\ UNCHANGED Inv4706_val
    /\ UNCHANGED Inv4707_val
    /\ UNCHANGED Inv4708_val
    /\ UNCHANGED Inv4709_val
    /\ UNCHANGED Inv4710_val
    /\ UNCHANGED Inv4711_val
    /\ UNCHANGED Inv4712_val
    /\ UNCHANGED Inv4713_val
    /\ UNCHANGED Inv4714_val
    /\ UNCHANGED Inv4715_val
    /\ UNCHANGED Inv4716_val
    /\ UNCHANGED Inv4717_val
    /\ UNCHANGED Inv4718_val
    /\ UNCHANGED Inv4719_val
    /\ UNCHANGED Inv4720_val
    /\ UNCHANGED Inv4721_val
    /\ UNCHANGED Inv4722_val
    /\ UNCHANGED Inv4723_val
    /\ UNCHANGED Inv4724_val
    /\ UNCHANGED Inv4725_val
    /\ UNCHANGED Inv4726_val
    /\ UNCHANGED Inv4728_val
    /\ UNCHANGED Inv4729_val
    /\ UNCHANGED Inv473_val
    /\ UNCHANGED Inv4733_val
    /\ UNCHANGED Inv4735_val
    /\ UNCHANGED Inv4736_val
    /\ UNCHANGED Inv4738_val
    /\ UNCHANGED Inv4739_val
    /\ UNCHANGED Inv4740_val
    /\ UNCHANGED Inv4741_val
    /\ UNCHANGED Inv4742_val
    /\ UNCHANGED Inv4743_val
    /\ UNCHANGED Inv4744_val
    /\ UNCHANGED Inv4745_val
    /\ UNCHANGED Inv4748_val
    /\ UNCHANGED Inv4749_val
    /\ UNCHANGED Inv475_val
    /\ UNCHANGED Inv4751_val
    /\ UNCHANGED Inv4758_val
    /\ UNCHANGED Inv4759_val
    /\ UNCHANGED Inv476_val
    /\ UNCHANGED Inv4760_val
    /\ UNCHANGED Inv4761_val
    /\ UNCHANGED Inv4762_val
    /\ UNCHANGED Inv4763_val
    /\ UNCHANGED Inv4764_val
    /\ UNCHANGED Inv4765_val
    /\ UNCHANGED Inv4766_val
    /\ UNCHANGED Inv4767_val
    /\ UNCHANGED Inv4768_val
    /\ UNCHANGED Inv4769_val
    /\ UNCHANGED Inv4770_val
    /\ UNCHANGED Inv4771_val
    /\ UNCHANGED Inv4772_val
    /\ UNCHANGED Inv4773_val
    /\ UNCHANGED Inv4774_val
    /\ UNCHANGED Inv4775_val
    /\ UNCHANGED Inv4776_val
    /\ UNCHANGED Inv4777_val
    /\ UNCHANGED Inv4778_val
    /\ UNCHANGED Inv4779_val
    /\ UNCHANGED Inv4780_val
    /\ UNCHANGED Inv4781_val
    /\ UNCHANGED Inv4782_val
    /\ UNCHANGED Inv4783_val
    /\ UNCHANGED Inv4784_val
    /\ UNCHANGED Inv4785_val
    /\ UNCHANGED Inv4786_val
    /\ UNCHANGED Inv4789_val
    /\ UNCHANGED Inv479_val
    /\ UNCHANGED Inv4790_val
    /\ UNCHANGED Inv4791_val
    /\ UNCHANGED Inv4792_val
    /\ UNCHANGED Inv4794_val
    /\ UNCHANGED Inv4796_val
    /\ UNCHANGED Inv4797_val
    /\ UNCHANGED Inv4798_val
    /\ UNCHANGED Inv4799_val
    /\ UNCHANGED Inv480_val
    /\ UNCHANGED Inv4800_val
    /\ UNCHANGED Inv4801_val
    /\ UNCHANGED Inv4802_val
    /\ UNCHANGED Inv4803_val
    /\ UNCHANGED Inv4804_val
    /\ UNCHANGED Inv4805_val
    /\ UNCHANGED Inv4806_val
    /\ UNCHANGED Inv4807_val
    /\ UNCHANGED Inv4809_val
    /\ UNCHANGED Inv4819_val
    /\ UNCHANGED Inv482_val
    /\ UNCHANGED Inv4820_val
    /\ UNCHANGED Inv4821_val
    /\ UNCHANGED Inv4823_val
    /\ UNCHANGED Inv4827_val
    /\ UNCHANGED Inv4828_val
    /\ UNCHANGED Inv4831_val
    /\ UNCHANGED Inv4833_val
    /\ UNCHANGED Inv4837_val
    /\ UNCHANGED Inv4839_val
    /\ UNCHANGED Inv4840_val
    /\ UNCHANGED Inv4841_val
    /\ UNCHANGED Inv4842_val
    /\ UNCHANGED Inv4844_val
    /\ UNCHANGED Inv4847_val
    /\ UNCHANGED Inv485_val
    /\ UNCHANGED Inv4850_val
    /\ UNCHANGED Inv4854_val
    /\ UNCHANGED Inv4858_val
    /\ UNCHANGED Inv4859_val
    /\ UNCHANGED Inv4861_val
    /\ UNCHANGED Inv4865_val
    /\ UNCHANGED Inv4868_val
    /\ UNCHANGED Inv4869_val
    /\ UNCHANGED Inv487_val
    /\ UNCHANGED Inv4872_val
    /\ UNCHANGED Inv4874_val
    /\ UNCHANGED Inv4875_val
    /\ UNCHANGED Inv4877_val
    /\ UNCHANGED Inv4879_val
    /\ UNCHANGED Inv488_val
    /\ UNCHANGED Inv4881_val
    /\ UNCHANGED Inv4883_val
    /\ UNCHANGED Inv4884_val
    /\ UNCHANGED Inv4885_val
    /\ UNCHANGED Inv4887_val
    /\ UNCHANGED Inv4889_val
    /\ UNCHANGED Inv489_val
    /\ UNCHANGED Inv4890_val
    /\ UNCHANGED Inv4891_val
    /\ UNCHANGED Inv4892_val
    /\ UNCHANGED Inv4893_val
    /\ UNCHANGED Inv4894_val
    /\ UNCHANGED Inv4895_val
    /\ UNCHANGED Inv4896_val
    /\ UNCHANGED Inv4897_val
    /\ UNCHANGED Inv4898_val
    /\ UNCHANGED Inv4899_val
    /\ UNCHANGED Inv4901_val
    /\ UNCHANGED Inv4902_val
    /\ UNCHANGED Inv4903_val
    /\ UNCHANGED Inv4904_val
    /\ UNCHANGED Inv4905_val
    /\ UNCHANGED Inv4906_val
    /\ UNCHANGED Inv4910_val
    /\ UNCHANGED Inv4912_val
    /\ UNCHANGED Inv4914_val
    /\ UNCHANGED Inv4919_val
    /\ UNCHANGED Inv4922_val
    /\ UNCHANGED Inv4924_val
    /\ UNCHANGED Inv4925_val
    /\ UNCHANGED Inv4929_val
    /\ UNCHANGED Inv4933_val
    /\ UNCHANGED Inv4935_val
    /\ UNCHANGED Inv4937_val
    /\ UNCHANGED Inv4939_val
    /\ UNCHANGED Inv4940_val
    /\ UNCHANGED Inv4941_val
    /\ UNCHANGED Inv4942_val
    /\ UNCHANGED Inv4943_val
    /\ UNCHANGED Inv4945_val
    /\ UNCHANGED Inv4946_val
    /\ UNCHANGED Inv4949_val
    /\ UNCHANGED Inv4950_val
    /\ UNCHANGED Inv4951_val
    /\ UNCHANGED Inv4955_val
    /\ UNCHANGED Inv4956_val
    /\ UNCHANGED Inv4957_val
    /\ UNCHANGED Inv4958_val
    /\ UNCHANGED Inv4959_val
    /\ UNCHANGED Inv4960_val
    /\ UNCHANGED Inv4961_val
    /\ UNCHANGED Inv4962_val
    /\ UNCHANGED Inv4963_val
    /\ UNCHANGED Inv4964_val
    /\ UNCHANGED Inv4965_val
    /\ UNCHANGED Inv4966_val
    /\ UNCHANGED Inv4967_val
    /\ UNCHANGED Inv4968_val
    /\ UNCHANGED Inv4969_val
    /\ UNCHANGED Inv4970_val
    /\ UNCHANGED Inv4971_val
    /\ UNCHANGED Inv4972_val
    /\ UNCHANGED Inv4973_val
    /\ UNCHANGED Inv4974_val
    /\ UNCHANGED Inv4975_val
    /\ UNCHANGED Inv4976_val
    /\ UNCHANGED Inv4977_val
    /\ UNCHANGED Inv4978_val
    /\ UNCHANGED Inv4979_val
    /\ UNCHANGED Inv4980_val
    /\ UNCHANGED Inv4981_val
    /\ UNCHANGED Inv4982_val
    /\ UNCHANGED Inv4983_val
    /\ UNCHANGED Inv4984_val
    /\ UNCHANGED Inv4985_val
    /\ UNCHANGED Inv4986_val
    /\ UNCHANGED Inv4987_val
    /\ UNCHANGED Inv4988_val
    /\ UNCHANGED Inv4989_val
    /\ UNCHANGED Inv4990_val
    /\ UNCHANGED Inv4991_val
    /\ UNCHANGED Inv4992_val
    /\ UNCHANGED Inv4993_val
    /\ UNCHANGED Inv4994_val
    /\ UNCHANGED Inv4995_val
    /\ UNCHANGED Inv4998_val
    /\ UNCHANGED Inv4999_val
    /\ UNCHANGED Inv5_val
    /\ UNCHANGED Inv500_val
    /\ UNCHANGED Inv5001_val
    /\ UNCHANGED Inv5002_val
    /\ UNCHANGED Inv5003_val
    /\ UNCHANGED Inv5007_val
    /\ UNCHANGED Inv5008_val
    /\ UNCHANGED Inv5009_val
    /\ UNCHANGED Inv5010_val
    /\ UNCHANGED Inv5011_val
    /\ UNCHANGED Inv5014_val
    /\ UNCHANGED Inv5015_val
    /\ UNCHANGED Inv5016_val
    /\ UNCHANGED Inv5017_val
    /\ UNCHANGED Inv5018_val
    /\ UNCHANGED Inv5019_val
    /\ UNCHANGED Inv5020_val
    /\ UNCHANGED Inv5021_val
    /\ UNCHANGED Inv5022_val
    /\ UNCHANGED Inv5023_val
    /\ UNCHANGED Inv5024_val
    /\ UNCHANGED Inv5025_val
    /\ UNCHANGED Inv5026_val
    /\ UNCHANGED Inv5027_val
    /\ UNCHANGED Inv5028_val
    /\ UNCHANGED Inv5029_val
    /\ UNCHANGED Inv5030_val
    /\ UNCHANGED Inv5031_val
    /\ UNCHANGED Inv5034_val
    /\ UNCHANGED Inv5035_val
    /\ UNCHANGED Inv5036_val
    /\ UNCHANGED Inv5037_val
    /\ UNCHANGED Inv5040_val
    /\ UNCHANGED Inv5041_val
    /\ UNCHANGED Inv5042_val
    /\ UNCHANGED Inv5043_val
    /\ UNCHANGED Inv5049_val
    /\ UNCHANGED Inv505_val
    /\ UNCHANGED Inv5050_val
    /\ UNCHANGED Inv5051_val
    /\ UNCHANGED Inv5052_val
    /\ UNCHANGED Inv5054_val
    /\ UNCHANGED Inv5055_val
    /\ UNCHANGED Inv5056_val
    /\ UNCHANGED Inv5058_val
    /\ UNCHANGED Inv5059_val
    /\ UNCHANGED Inv506_val
    /\ UNCHANGED Inv5060_val
    /\ UNCHANGED Inv5061_val
    /\ UNCHANGED Inv5062_val
    /\ UNCHANGED Inv5063_val
    /\ UNCHANGED Inv5064_val
    /\ UNCHANGED Inv5065_val
    /\ UNCHANGED Inv5066_val
    /\ UNCHANGED Inv5067_val
    /\ UNCHANGED Inv5068_val
    /\ UNCHANGED Inv5069_val
    /\ UNCHANGED Inv5070_val
    /\ UNCHANGED Inv5071_val
    /\ UNCHANGED Inv5072_val
    /\ UNCHANGED Inv5073_val
    /\ UNCHANGED Inv5074_val
    /\ UNCHANGED Inv5075_val
    /\ UNCHANGED Inv5076_val
    /\ UNCHANGED Inv5077_val
    /\ UNCHANGED Inv5078_val
    /\ UNCHANGED Inv5079_val
    /\ UNCHANGED Inv5080_val
    /\ UNCHANGED Inv5081_val
    /\ UNCHANGED Inv5082_val
    /\ UNCHANGED Inv5083_val
    /\ UNCHANGED Inv5084_val
    /\ UNCHANGED Inv5085_val
    /\ UNCHANGED Inv5086_val
    /\ UNCHANGED Inv5087_val
    /\ UNCHANGED Inv5088_val
    /\ UNCHANGED Inv5089_val
    /\ UNCHANGED Inv5090_val
    /\ UNCHANGED Inv5091_val
    /\ UNCHANGED Inv5092_val
    /\ UNCHANGED Inv5093_val
    /\ UNCHANGED Inv5094_val
    /\ UNCHANGED Inv5095_val
    /\ UNCHANGED Inv5099_val
    /\ UNCHANGED Inv5101_val
    /\ UNCHANGED Inv5102_val
    /\ UNCHANGED Inv5103_val
    /\ UNCHANGED Inv5104_val
    /\ UNCHANGED Inv5105_val
    /\ UNCHANGED Inv5106_val
    /\ UNCHANGED Inv5107_val
    /\ UNCHANGED Inv5108_val
    /\ UNCHANGED Inv5109_val
    /\ UNCHANGED Inv511_val
    /\ UNCHANGED Inv5110_val
    /\ UNCHANGED Inv5111_val
    /\ UNCHANGED Inv5112_val
    /\ UNCHANGED Inv5113_val
    /\ UNCHANGED Inv5114_val
    /\ UNCHANGED Inv5115_val
    /\ UNCHANGED Inv512_val
    /\ UNCHANGED Inv5122_val
    /\ UNCHANGED Inv5123_val
    /\ UNCHANGED Inv5124_val
    /\ UNCHANGED Inv5127_val
    /\ UNCHANGED Inv5128_val
    /\ UNCHANGED Inv5130_val
    /\ UNCHANGED Inv5135_val
    /\ UNCHANGED Inv5138_val
    /\ UNCHANGED Inv5139_val
    /\ UNCHANGED Inv514_val
    /\ UNCHANGED Inv5141_val
    /\ UNCHANGED Inv5142_val
    /\ UNCHANGED Inv5146_val
    /\ UNCHANGED Inv515_val
    /\ UNCHANGED Inv5158_val
    /\ UNCHANGED Inv5159_val
    /\ UNCHANGED Inv5162_val
    /\ UNCHANGED Inv5163_val
    /\ UNCHANGED Inv5164_val
    /\ UNCHANGED Inv5165_val
    /\ UNCHANGED Inv5166_val
    /\ UNCHANGED Inv5167_val
    /\ UNCHANGED Inv5168_val
    /\ UNCHANGED Inv5173_val
    /\ UNCHANGED Inv5175_val
    /\ UNCHANGED Inv5176_val
    /\ UNCHANGED Inv5178_val
    /\ UNCHANGED Inv5180_val
    /\ UNCHANGED Inv5184_val
    /\ UNCHANGED Inv5188_val
    /\ UNCHANGED Inv5190_val
    /\ UNCHANGED Inv5191_val
    /\ UNCHANGED Inv5192_val
    /\ UNCHANGED Inv5193_val
    /\ UNCHANGED Inv5196_val
    /\ UNCHANGED Inv5197_val
    /\ UNCHANGED Inv52_val
    /\ UNCHANGED Inv5200_val
    /\ UNCHANGED Inv5202_val
    /\ UNCHANGED Inv5203_val
    /\ UNCHANGED Inv5204_val
    /\ UNCHANGED Inv5205_val
    /\ UNCHANGED Inv5207_val
    /\ UNCHANGED Inv5209_val
    /\ UNCHANGED Inv5210_val
    /\ UNCHANGED Inv5212_val
    /\ UNCHANGED Inv5213_val
    /\ UNCHANGED Inv5215_val
    /\ UNCHANGED Inv5217_val
    /\ UNCHANGED Inv5219_val
    /\ UNCHANGED Inv522_val
    /\ UNCHANGED Inv5222_val
    /\ UNCHANGED Inv5225_val
    /\ UNCHANGED Inv5228_val
    /\ UNCHANGED Inv5229_val
    /\ UNCHANGED Inv523_val
    /\ UNCHANGED Inv5230_val
    /\ UNCHANGED Inv5231_val
    /\ UNCHANGED Inv5236_val
    /\ UNCHANGED Inv5237_val
    /\ UNCHANGED Inv5238_val
    /\ UNCHANGED Inv5239_val
    /\ UNCHANGED Inv524_val
    /\ UNCHANGED Inv5241_val
    /\ UNCHANGED Inv5242_val
    /\ UNCHANGED Inv5243_val
    /\ UNCHANGED Inv5244_val
    /\ UNCHANGED Inv5245_val
    /\ UNCHANGED Inv5248_val
    /\ UNCHANGED Inv5249_val
    /\ UNCHANGED Inv5251_val
    /\ UNCHANGED Inv5254_val
    /\ UNCHANGED Inv5256_val
    /\ UNCHANGED Inv5257_val
    /\ UNCHANGED Inv5258_val
    /\ UNCHANGED Inv5259_val
    /\ UNCHANGED Inv5260_val
    /\ UNCHANGED Inv5261_val
    /\ UNCHANGED Inv5262_val
    /\ UNCHANGED Inv5263_val
    /\ UNCHANGED Inv5264_val
    /\ UNCHANGED Inv5265_val
    /\ UNCHANGED Inv5266_val
    /\ UNCHANGED Inv5267_val
    /\ UNCHANGED Inv5268_val
    /\ UNCHANGED Inv5269_val
    /\ UNCHANGED Inv5270_val
    /\ UNCHANGED Inv5271_val
    /\ UNCHANGED Inv5272_val
    /\ UNCHANGED Inv5273_val
    /\ UNCHANGED Inv5274_val
    /\ UNCHANGED Inv5275_val
    /\ UNCHANGED Inv5276_val
    /\ UNCHANGED Inv5277_val
    /\ UNCHANGED Inv5278_val
    /\ UNCHANGED Inv5279_val
    /\ UNCHANGED Inv5280_val
    /\ UNCHANGED Inv5281_val
    /\ UNCHANGED Inv5282_val
    /\ UNCHANGED Inv5283_val
    /\ UNCHANGED Inv5284_val
    /\ UNCHANGED Inv5285_val
    /\ UNCHANGED Inv5286_val
    /\ UNCHANGED Inv5287_val
    /\ UNCHANGED Inv5288_val
    /\ UNCHANGED Inv5289_val
    /\ UNCHANGED Inv5290_val
    /\ UNCHANGED Inv5291_val
    /\ UNCHANGED Inv5292_val
    /\ UNCHANGED Inv5293_val
    /\ UNCHANGED Inv5294_val
    /\ UNCHANGED Inv5295_val
    /\ UNCHANGED Inv5296_val
    /\ UNCHANGED Inv5297_val
    /\ UNCHANGED Inv5298_val
    /\ UNCHANGED Inv5299_val
    /\ UNCHANGED Inv530_val
    /\ UNCHANGED Inv5300_val
    /\ UNCHANGED Inv5304_val
    /\ UNCHANGED Inv5305_val
    /\ UNCHANGED Inv5306_val
    /\ UNCHANGED Inv5308_val
    /\ UNCHANGED Inv5312_val
    /\ UNCHANGED Inv5313_val
    /\ UNCHANGED Inv5314_val
    /\ UNCHANGED Inv5315_val
    /\ UNCHANGED Inv5316_val
    /\ UNCHANGED Inv5317_val
    /\ UNCHANGED Inv5318_val
    /\ UNCHANGED Inv5319_val
    /\ UNCHANGED Inv5320_val
    /\ UNCHANGED Inv5321_val
    /\ UNCHANGED Inv5322_val
    /\ UNCHANGED Inv5323_val
    /\ UNCHANGED Inv5324_val
    /\ UNCHANGED Inv5325_val
    /\ UNCHANGED Inv5326_val
    /\ UNCHANGED Inv5327_val
    /\ UNCHANGED Inv5328_val
    /\ UNCHANGED Inv5329_val
    /\ UNCHANGED Inv5330_val
    /\ UNCHANGED Inv5331_val
    /\ UNCHANGED Inv5332_val
    /\ UNCHANGED Inv5333_val
    /\ UNCHANGED Inv5334_val
    /\ UNCHANGED Inv5336_val
    /\ UNCHANGED Inv5338_val
    /\ UNCHANGED Inv5339_val
    /\ UNCHANGED Inv5341_val
    /\ UNCHANGED Inv5343_val
    /\ UNCHANGED Inv5344_val
    /\ UNCHANGED Inv5346_val
    /\ UNCHANGED Inv5347_val
    /\ UNCHANGED Inv5349_val
    /\ UNCHANGED Inv5350_val
    /\ UNCHANGED Inv5351_val
    /\ UNCHANGED Inv5352_val
    /\ UNCHANGED Inv5353_val
    /\ UNCHANGED Inv5354_val
    /\ UNCHANGED Inv5355_val
    /\ UNCHANGED Inv5356_val
    /\ UNCHANGED Inv5357_val
    /\ UNCHANGED Inv5358_val
    /\ UNCHANGED Inv5359_val
    /\ UNCHANGED Inv536_val
    /\ UNCHANGED Inv5360_val
    /\ UNCHANGED Inv5361_val
    /\ UNCHANGED Inv5362_val
    /\ UNCHANGED Inv5363_val
    /\ UNCHANGED Inv5364_val
    /\ UNCHANGED Inv5365_val
    /\ UNCHANGED Inv5366_val
    /\ UNCHANGED Inv5367_val
    /\ UNCHANGED Inv5368_val
    /\ UNCHANGED Inv5369_val
    /\ UNCHANGED Inv537_val
    /\ UNCHANGED Inv5370_val
    /\ UNCHANGED Inv5371_val
    /\ UNCHANGED Inv5372_val
    /\ UNCHANGED Inv5373_val
    /\ UNCHANGED Inv5374_val
    /\ UNCHANGED Inv5375_val
    /\ UNCHANGED Inv5376_val
    /\ UNCHANGED Inv5377_val
    /\ UNCHANGED Inv5378_val
    /\ UNCHANGED Inv5379_val
    /\ UNCHANGED Inv5381_val
    /\ UNCHANGED Inv5383_val
    /\ UNCHANGED Inv5384_val
    /\ UNCHANGED Inv5386_val
    /\ UNCHANGED Inv5387_val
    /\ UNCHANGED Inv5388_val
    /\ UNCHANGED Inv5389_val
    /\ UNCHANGED Inv5390_val
    /\ UNCHANGED Inv5391_val
    /\ UNCHANGED Inv5392_val
    /\ UNCHANGED Inv5393_val
    /\ UNCHANGED Inv5394_val
    /\ UNCHANGED Inv5395_val
    /\ UNCHANGED Inv5396_val
    /\ UNCHANGED Inv5397_val
    /\ UNCHANGED Inv540_val
    /\ UNCHANGED Inv5402_val
    /\ UNCHANGED Inv5404_val
    /\ UNCHANGED Inv5405_val
    /\ UNCHANGED Inv541_val
    /\ UNCHANGED Inv5415_val
    /\ UNCHANGED Inv5416_val
    /\ UNCHANGED Inv542_val
    /\ UNCHANGED Inv5422_val
    /\ UNCHANGED Inv5423_val
    /\ UNCHANGED Inv5428_val
    /\ UNCHANGED Inv5433_val
    /\ UNCHANGED Inv5434_val
    /\ UNCHANGED Inv5435_val
    /\ UNCHANGED Inv5437_val
    /\ UNCHANGED Inv5438_val
    /\ UNCHANGED Inv5440_val
    /\ UNCHANGED Inv5442_val
    /\ UNCHANGED Inv5443_val
    /\ UNCHANGED Inv5444_val
    /\ UNCHANGED Inv5447_val
    /\ UNCHANGED Inv5448_val
    /\ UNCHANGED Inv5452_val
    /\ UNCHANGED Inv5454_val
    /\ UNCHANGED Inv5456_val
    /\ UNCHANGED Inv5457_val
    /\ UNCHANGED Inv5458_val
    /\ UNCHANGED Inv5459_val
    /\ UNCHANGED Inv5460_val
    /\ UNCHANGED Inv5461_val
    /\ UNCHANGED Inv5470_val
    /\ UNCHANGED Inv5475_val
    /\ UNCHANGED Inv5479_val
    /\ UNCHANGED Inv548_val
    /\ UNCHANGED Inv5480_val
    /\ UNCHANGED Inv5481_val
    /\ UNCHANGED Inv5482_val
    /\ UNCHANGED Inv5483_val
    /\ UNCHANGED Inv5486_val
    /\ UNCHANGED Inv549_val
    /\ UNCHANGED Inv5494_val
    /\ UNCHANGED Inv5498_val
    /\ UNCHANGED Inv5499_val
    /\ UNCHANGED Inv550_val
    /\ UNCHANGED Inv5501_val
    /\ UNCHANGED Inv5504_val
    /\ UNCHANGED Inv5506_val
    /\ UNCHANGED Inv5507_val
    /\ UNCHANGED Inv5508_val
    /\ UNCHANGED Inv5511_val
    /\ UNCHANGED Inv5512_val
    /\ UNCHANGED Inv5520_val
    /\ UNCHANGED Inv5521_val
    /\ UNCHANGED Inv5522_val
    /\ UNCHANGED Inv5523_val
    /\ UNCHANGED Inv5524_val
    /\ UNCHANGED Inv5525_val
    /\ UNCHANGED Inv5526_val
    /\ UNCHANGED Inv5527_val
    /\ UNCHANGED Inv5528_val
    /\ UNCHANGED Inv5529_val
    /\ UNCHANGED Inv5530_val
    /\ UNCHANGED Inv5531_val
    /\ UNCHANGED Inv5532_val
    /\ UNCHANGED Inv5533_val
    /\ UNCHANGED Inv5534_val
    /\ UNCHANGED Inv5535_val
    /\ UNCHANGED Inv5536_val
    /\ UNCHANGED Inv5537_val
    /\ UNCHANGED Inv5538_val
    /\ UNCHANGED Inv5539_val
    /\ UNCHANGED Inv554_val
    /\ UNCHANGED Inv5540_val
    /\ UNCHANGED Inv5541_val
    /\ UNCHANGED Inv5542_val
    /\ UNCHANGED Inv5543_val
    /\ UNCHANGED Inv5544_val
    /\ UNCHANGED Inv5545_val
    /\ UNCHANGED Inv5546_val
    /\ UNCHANGED Inv5549_val
    /\ UNCHANGED Inv5551_val
    /\ UNCHANGED Inv5552_val
    /\ UNCHANGED Inv5553_val
    /\ UNCHANGED Inv5554_val
    /\ UNCHANGED Inv5556_val
    /\ UNCHANGED Inv5557_val
    /\ UNCHANGED Inv5558_val
    /\ UNCHANGED Inv556_val
    /\ UNCHANGED Inv5560_val
    /\ UNCHANGED Inv5562_val
    /\ UNCHANGED Inv5563_val
    /\ UNCHANGED Inv5564_val
    /\ UNCHANGED Inv5565_val
    /\ UNCHANGED Inv5566_val
    /\ UNCHANGED Inv5567_val
    /\ UNCHANGED Inv5568_val
    /\ UNCHANGED Inv5569_val
    /\ UNCHANGED Inv5570_val
    /\ UNCHANGED Inv5571_val
    /\ UNCHANGED Inv5572_val
    /\ UNCHANGED Inv5573_val
    /\ UNCHANGED Inv5574_val
    /\ UNCHANGED Inv5575_val
    /\ UNCHANGED Inv5577_val
    /\ UNCHANGED Inv558_val
    /\ UNCHANGED Inv5580_val
    /\ UNCHANGED Inv5582_val
    /\ UNCHANGED Inv5583_val
    /\ UNCHANGED Inv5584_val
    /\ UNCHANGED Inv5591_val
    /\ UNCHANGED Inv5592_val
    /\ UNCHANGED Inv5594_val
    /\ UNCHANGED Inv5595_val
    /\ UNCHANGED Inv5596_val
    /\ UNCHANGED Inv5597_val
    /\ UNCHANGED Inv5598_val
    /\ UNCHANGED Inv5599_val
    /\ UNCHANGED Inv56_val
    /\ UNCHANGED Inv5600_val
    /\ UNCHANGED Inv5601_val
    /\ UNCHANGED Inv5602_val
    /\ UNCHANGED Inv5603_val
    /\ UNCHANGED Inv5604_val
====
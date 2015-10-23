#region Using Statements
using System;
using Microsoft.Xna.Framework;
using Microsoft.Xna.Framework.Graphics;
using Microsoft.Xna.Framework.Storage;
using Microsoft.Xna.Framework.Input;
	
#endregion

namespace NewGame
{
	/// <summary>
    /// This is the main type for your game
    /// </summary>
    public class Game1 : Microsoft.Xna.Framework.Game
    {
        GraphicsDeviceManager graphics;
        SpriteBatch spriteBatch;		
		private static readonly int ROWS = 10;
		private static readonly int COLS = 10;
		bool[,] gameBoard = new bool[ROWS,COLS];

		Texture2D cellSprite;

		public void Clear(bool[,] board){
			for(int i = 0; i < ROWS; ++i){
				for(int j = 0; j < COLS; ++j){
					board[i,j] = false;
				}
			}
		}
			
		public Game1()
        {
            graphics = new GraphicsDeviceManager(this);
            Content.RootDirectory = "Content";	            
			graphics.IsFullScreen = true;		
        }

        /// <summary>
        /// Allows the game to perform any initialization it needs to before starting to run.
        /// This is where it can query for any required services and load any non-graphic
        /// related content.  Calling base.Initialize will enumerate through any components
        /// and initialize them as well.
        /// </summary>
        protected override void Initialize()
        {
            // TODO: Add your initialization logic here
            base.Initialize();
			Clear (gameBoard);
        }

        /// <summary>
        /// LoadContent will be called once per game and is the place to load
        /// all of your content.
        /// </summary>
        protected override void LoadContent()
        {
            // Create a new SpriteBatch, which can be used to draw textures.
            spriteBatch = new SpriteBatch(GraphicsDevice);
			cellSprite = Content.Load<Texture2D> ("/home/john/Prog/c#/MonoDevelop/Game/Game/SquareGuy.png");

            //TODO: use this.Content to load your game content here 
        }

        /// <summary>
        /// Allows the game to run logic such as updating the world,
        /// checking for collisions, gathering input, and playing audio.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Update(GameTime gameTime)
        {
            // For Mobile devices, this logic will close the Game when the Back button is pressed
            if (GamePad.GetState(PlayerIndex.One).Buttons.Back == ButtonState.Pressed)
			{
				Exit();
			}
            // TODO: Add your update logic here			
            base.Update(gameTime);
        }

        /// <summary>
        /// This is called when the game should draw itself.
        /// </summary>
        /// <param name="gameTime">Provides a snapshot of timing values.</param>
        protected override void Draw(GameTime gameTime)
        {
           	graphics.GraphicsDevice.Clear(Color.CornflowerBlue);
		
			spriteBatch.Begin ();
			for(int i = 0; i < ROWS; ++i){
				for(int j = 0; j < COLS; ++j){
					Vector2 pos = new Vector2 ();
					pos.X = j * cellSprite.Width;
					pos.Y = i * cellSprite.Height;
					if (gameBoard [i, j]) {
						spriteBatch.Draw (cellSprite, pos, Color.Black);
					}else {
						spriteBatch.Draw (cellSprite, pos, Color.Red);
					}
				}
			}

			spriteBatch.End ();
            
            base.Draw(gameTime);
        }
    }
}


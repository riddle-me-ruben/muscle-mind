import os
import pymysql
from flask import Flask, request, redirect, url_for, render_template
from dotenv import load_dotenv

# Load environment variables from the .env file
load_dotenv()

# Adjust the app initialization
app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')

# Database configuration
app.config['MYSQL_HOST'] = os.getenv('MYSQL_HOST')
app.config['MYSQL_USER'] = os.getenv('MYSQL_USER')
app.config['MYSQL_PASSWORD'] = os.getenv('MYSQL_PASSWORD')
app.config['MYSQL_DB'] = os.getenv('MYSQL_DB')
app.config['MYSQL_PORT'] = int(os.getenv('MYSQL_PORT'))

# Create a connection to the database
# @ requires working database
# @ ensures connection is returned
def get_db_connection():
    connection = pymysql.connect(
        host=app.config['MYSQL_HOST'],
        user=app.config['MYSQL_USER'],
        password=app.config['MYSQL_PASSWORD'],
        database=app.config['MYSQL_DB'],
        port=app.config['MYSQL_PORT']
    )
    return connection

@app.route('/')
def index():
    return render_template('index.html')  # Render the HTML file as a Jinja template

@app.route('/add_user', methods=['POST'])
def add_user():
    email = request.form['email']
    password = request.form['password']

    # Check if the email already exists
    connection = get_db_connection()
    cursor = connection.cursor()

    cursor.execute("SELECT * FROM users WHERE email = %s", (email,))
    existing_user = cursor.fetchone()

    if existing_user:
        cursor.close()
        connection.close()
        # Return the form with an error message
        return render_template('index.html', error2="Email already exists.")

    # If email does not exist, insert the new user
    cursor.execute("INSERT INTO users (email, password) VALUES (%s, %s)", (email, password))
    connection.commit()
    cursor.close()
    connection.close()

    # Return the form with a success message
    return render_template('index.html', success2="Registration successful! You may now log in.")

@app.route('/login', methods=['GET'])
def login():
    return render_template('login.html', error=None)

@app.route('/login', methods=['POST'])
def login_user():
    email = request.form['email']
    password = request.form['password']

    # Check if the user exists
    connection = get_db_connection()
    cursor = connection.cursor()

    cursor.execute("SELECT * FROM users WHERE email = %s AND password = %s", (email, password))
    user = cursor.fetchone()

    cursor.close()
    connection.close()

    if user:
        return redirect(url_for('home'))  # Redirect to home page on successful login
    else:
        return render_template('login.html', error='Invalid email or password.')

@app.route('/home')
def home():
    return render_template('home.html')  # Render the home page as a Jinja template

if __name__ == '__main__':
    app.run(debug=True)
